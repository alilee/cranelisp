# Platform — master design

`crates/cranelisp-platform/` — the shared interface contract between the
cranelisp host binary and every platform DLL. Both sides depend on this crate;
that is its purpose. It owns the C-ABI types, the safe wrappers that present
them in Rust, the layout constants both sides agree on, the macro a DLL uses to
publish its manifest, the parser for the generated schema artifact, and the
marshalling helpers that keep RC discipline correct across the boundary.

**This document carries the crate's shape and its invariants.** Per-item public
truth is the source rustdoc plus `public-api.txt`; this document does not
re-derive an item list, a file census or a line count. Counts are not design
invariants and predictably decay.

**Subordinate documents:** `platform-dlls.md` (authoring and loading mechanics),
`poll-leaf-authoring.md` (the poll-shape contract), `adt-marker-binding.md` (the
marker mechanism decision).

---

## 1. Bounded context

Per `design/arch/bounded-contexts.md` §5, platform is the **shared interface
contract crate**. It owns no session-coordinated state and no cadence: it spawns
no thread, runs no state machine, and makes no scheduling decision.

**Owns**

- **ABI value wrappers** — the `CLType` trait and `CLInt`/`CLBool`/`CLFloat`/
  `CLString`, `CLIO<T>`, `CLOwned<T>`, the `CLHeap` trait.
- **ADT marshalling** — `CLAdt<T>`, the `CLAdtType` marker trait,
  `CLTypeWitness`/`ExpectedFieldType`, and name-keyed field access over the
  embedded schema.
- **C-ABI contract types** — `PlatformManifest`, `PlatformFn`, `HostCallbacks`,
  `EffectOutcome`, all `#[repr(C)]`.
- **Host-reactor C-ABI** — `HostCtx`, `Waker`, `WakerVTable`, `PollFn`, plus the
  `cranelisp_types` re-exports they need. Core and ungated.
- **Layout constants** — `ABI_VERSION`, the `IO_TAG_*` family, `HEAP_HEADER_SIZE`,
  `STRING_HEADER_BYTES`, and the payload offsets in §4.
- **The DLL-author macro** — `declare_platform!`, the single three-exports
  emitter, plus the const scanners it depends on.
- **The schema parser** — a small S-expression reader over the compiler-generated
  `/platform-schema` artifact, total and frontend-independent (Principle 3).
- **Leaf-author ergonomics** — the `poll_support` scaffolds.
- **Three per-DLL write-once globals** — the two allocator slots
  (`GLOBAL_ALLOC`, `GLOBAL_ALLOC_WITH_TAG`) and the schema `OnceLock`
  (`GLOBAL_SCHEMA`), each set once at DLL load and bounded by invariant 6 below.

**Does not own**

| Concern | Owner |
|---|---|
| DLL discovery, `dlopen`, ABI-version refusal, retention, lifecycle | `src/` (int) |
| Type-signature parsing into the typecheck vocabulary | `src/` (int) — keeps this crate free of a typecheck dependency |
| The IO trampoline, the reactor, teardown, the permit pool | `cranelisp-intrinsics` |
| Scheduling decisions | the trampoline, off the manifest facts int lifts |
| Platform-fn dispatch state | the host's `GotTable`, which wraps the DLL's exported GOT in place |
| IO semantics | `spec/10-io.md` |
| Per-DLL platform implementations | the DLL crates themselves |

**Crossing outward**: the C-ABI types, the wrappers, the constants and the
macro, to host and DLL alike. **Inward**: `SchedulingClass`, `HeapHeader` from
`cranelisp-types`. **Re-exported** under Principle 15's external-audience
exception: `SchedulingClass` and `PlatformError`, because an out-of-tree DLL
author depends only on this crate and has no other reason to learn about
`cranelisp-types`. This is the only crate in the workspace that exercises that
exception.

---

## 2. Public surface

The facade *is* the source rustdoc — the standalone facade document retired at
S71, the third instance of that pattern. The shape:

- **Marshalling layer.** `CLType` is sealed by convention: the four primitive
  wrappers and `CLAdt<T>` implement it, and **`CLIO<T>` deliberately does not**.
  That exclusion is load-bearing, not an oversight — it is what makes a nested
  `pure(pure(…))` unconstructable through the facade, so every DLL-minted IO node
  reaches the host as a platform call's return value (§4.1). `CLHeap: CLType +
  Copy` marks the RC-participating subset: `CLString` and `CLAdt<T>`.
- **Ownership vocabulary.** `CLHeap::own(&self)` increments (a borrowed read
  becomes an owned reference); `CLHeap::into_owned_consuming(self)` does not (a
  transferred reference becomes the `CLOwned`'s). `CLOwned<T>` decrements on
  drop. There is deliberately no `into_inner`: an owned reference leaves only by
  being dropped or by being handed on as a value.
- **Manifest layer.** `PlatformManifest` + `PlatformFn` + `HostCallbacks` +
  `EffectOutcome`, layout-stable contracts governed by `ABI_VERSION`.
  `manifest_to_descriptors` is the host-side conversion into the owned,
  UTF-8-validated `OwnedPlatformFnDescriptor`.
- **Author macro.** `declare_platform!`, in two arms — with an embedded schema
  and without.
- **Schema layer.** `Schema`/`TypeShape`/`Ctor`/`Field`/`FieldType` and the
  parser.
- **Poll layer.** The host-reactor contract types and the `poll_support`
  scaffolds.

Drift between facade and implementation is `cargo-public-api`'s job against
`public-api.txt`, and `review`'s per-change audit. It is not this document's.

---

## 3. Internal shape

Six cohesive modules, each one concern:

| Module | Concern |
|---|---|
| `lib.rs` | the wrapper family, the `#[repr(C)]` contract types, the constants, `HostContext`, `manifest_to_descriptors` |
| `declare.rs` | `declare_platform!` and the const scanners over the embedded artifact |
| `schema.rs` | the generated-artifact parser and its lookups |
| `adt.rs` | `CLAdt<T>`, the witness machinery, `GLOBAL_SCHEMA`, name→offset resolution |
| `concurrency.rs` | the host-reactor C-ABI — pure `#[repr(C)]` shape, with layout-stability pins |
| `poll_support.rs` | leaf-author ergonomics |

The crate has two *faces* — host and DLL — compiled from the same source. Each
loaded DLL gets its own copy of the per-DLL globals, because it is a separate
compilation unit; `HostContext::init` runs inside each DLL's manifest entry
point, and the host calls `manifest_to_descriptors` to read what that DLL
exposes.

Unsafe work is concentrated at the ABI and heap-wrapper seams and carries
explicit safety contracts. There is no internal cadence and no second path for
anything: one manifest type, one macro, one GOT export, one loader path, one
schema parser, one host-callback builder.

---

## 4. The ABI

Per spec §10.10.1 every value crosses the boundary as a single `i64`.

| Cranelisp type | `i64` interpretation | Wrapper |
|---|---|---|
| `Int` | the value | `CLInt` |
| `Bool` | 0 / 1 | `CLBool` |
| `Float` | `f64::to_ne_bytes` reinterpreted | `CLFloat` |
| `String` | base pointer to a heap allocation | `CLString` |
| ADT | base pointer to a tagged heap allocation | `CLAdt<T>` |
| `IO a` | base pointer to a heap IO node | `CLIO<T>` |

`Fn a b` has no row and will not gain one: there is **no closure-callback
capability across this boundary** (§5, invariant 3).

### 4.1 IO node layout

Every node is `[header (16 bytes) | tag | fields…]`. The constructors return the
**base** pointer, not the payload pointer, because the trampoline reads the tag
at `base + HEAP_HEADER_SIZE`.

| Constant | Tag | Payload | Fields | Constructed by |
|---|---:|---:|---|---|
| `IO_TAG_PURE` | 0 | **24** | `[tag, payload, payload_glue]` — glue at `IO_PURE_GLUE_OFFSET` (payload+16, base+32) | backend, and `CLIO::pure` in a DLL |
| `IO_TAG_EFFECT` | 1 | 40 | `[tag, thunk_ptr, resource_token, fn_name, capacity]` at payload offsets 0/8/16/24/32 | `CLIO::effect*` in a DLL |
| `IO_TAG_BIND` | 2 | — | `[tag, inner, cont]` | host |
| `IO_TAG_PAR` | 3 | — | `[tag, count, branch_0…]` | host |
| `IO_TAG_EFFECT_POLL` | 4 | — | `[tag, state_closure]` | backend |
| `IO_TAG_LAUNCH` | 5 | — | `[tag, sub-tree \| 0 sentinel]` | host |
| `IO_TAG_SELECT` | 6 | — | `[tag, branch carrier]` | host |

**The `Pure` payload-glue word** says what field 0 owes: `0 = Scalar` (nothing)
or `Owned(glue)`, the canonical `drop<T>` for the payload's concrete type. `1` is
reserved and emitted by nothing; it is not a platform tag, field or public
constant. The payload stays at field 0.

**Two writers, both before publication — the write authority at this seam.** A
DLL cannot supply a real glue address: those are host-process, per-concrete-type
values, and `HostCallbacks` has no channel to fetch one and will not gain one
(§5, invariant 3). The authority is therefore split:

| Stage | Who | What |
|---|---|---|
| **Initialise** | the DLL, in `CLIO::pure` | while the fresh node is exclusively owned and unpublished, writes the `0` sentinel and nothing else |
| **Stamp/adopt** | the backend | while the node remains exclusively owned and unpublished, writes `0` or the payload type's canonical `drop<T>`; at construction for a host-built node, and at the ABI crossing for a DLL-built one (§4.4) |

Nothing writes either word after publication. Forcing reads the word and mints
the consumer's reference, so one node may be forced any number of times, and
teardown discharges `Owned(glue)` once. That rule, and the handling of the
reserved `1`, are `intrinsics`' (`design/intrinsics/ownership-and-disposal.md`
§6.1); platform code implements no part of it.

The DLL's `0` is therefore not a claim about ownership: it is an initial value the
crossing replaces, exactly as the `Effect` node's null `fn_name` already is.

**Effect-node offsets are append-only.** Every widening so far appended;
nothing has ever moved. `fn_name` is initialised null by the DLL and stamped by
the host under the tag licence of §4.4, so an unstamped node degrades to
`"<unknown>"` rather than crashing.

### 4.2 Effect forcing

An `Effect` node is a reusable IO value: a program may force one node any
number of times, sequentially or from concurrent `Par` branches. The thunk is
therefore **repeatable and borrowed**, and its lifetime is the node's. The
approved surface is `arch`'s (`design/arch/total-concreteness.md` §3.4,
"`Effect` public-API delta"); this section is its interior.

**Ownership.** The node's `thunk_ptr` word is the sole owner of one heap thunk:
a double box (the outer box makes a thin pointer from the trait object) around
the DLL-built wrapper closure, which owns the author's closure and every
capture. One private type names that stored shape, and the constructor, the
force and the drop all use it, so the three cannot disagree about what the word
points to. The box carries no count of its own; the node's reference count
already covers every lane still able to force it.

| Operation | Who | What happens to the thunk |
|---|---|---|
| construct | `CLIO::effect*`, in the DLL | boxes the wrapper; writes its pointer into the fresh node |
| force | `call_effect_thunk`, host, any number of times, possibly concurrently | calls the wrapper through a shared reference; nothing is moved or freed |
| discharge | `drop_effect_thunk`, host, exactly once | reclaims and drops the box, running the capture destructors |

The author closure's bound, `Fn() -> CL + Send + Sync + 'static`, is what makes
this sound without a lock: `Fn` permits calls through a shared reference,
`Sync` permits two branches to make them at once, and `Send` permits the box to
be built on one thread and discharged on whichever thread releases the node.
The compiler rejects a capture that cannot meet them; the surface adds no
runtime check and no per-node lock (Principle 20).

**The wrapper, per force.** It calls the author closure by reference under
`catch_unwind`, converting a panic into an `EffectOutcome` fault. Because the
closure survives a caught panic, a later force of the same node runs it again; a capture left inconsistent by that panic is the author's
to guard (a `Mutex` capture poisons). A hardware trap that the host's signal
guard recovers from leaves the thunk intact, so discharge still runs.

**Discharge and capture-destructor containment.** Capture destructors run at
discharge, outside the per-force catch, and a DLL-originated unwind must
never reach host frames. The wrapper therefore holds the author closure in a
private containment holder whose destructor drops the closure under
`catch_unwind`. The holder is instantiated inside the generic constructor, so
its destructor — reached through the trait object's drop entry — is
monomorphised into the DLL and caught by the DLL's own runtime; unwinding drop
glue still drops the remaining captures. The caught payload is leaked rather
than dropped, so a payload whose own destructor panics cannot escape either;
that leak is bounded like the fault-cause bytes (§5 invariant 6). Nothing is
reported to the host: the effect's result has already been delivered, there is
no outcome channel at discharge, and `HostCallbacks` will not widen (§5
invariant 3). The DLL's panic hook has already printed the message. What the
panicking destructor failed to release stays leaked.

*Grade: asserted, with a named falsifier — not structural.* Building the holder
outside the generic constructor still compiles, and the platform unit test runs
in one panic runtime, so it proves the holder catches but not that the catch
runs on the DLL's side of a cdylib boundary. The falsifier is a real platform
DLL whose `Effect` capture panics in its destructor: discharge must leave the
host running with the DLL's panic message, not abort. The force path has that
measurement (`platforms/boom`); discharge does not. Whether a fixture earns its
cost is `qa`'s decision.

Aborting was rejected, because it would let one DLL destructor end the host
process when the force path already contains the same failure. A host-side
catch is impossible for the reason below.

The panic catch is **DLL-local** on both paths, and that is the only sound
arrangement: a platform cdylib statically links its own panic runtime, so a
host-side `catch_unwind` would see a DLL-originated unwind as a foreign
exception and abort, and `extern "C-unwind"` cannot bridge two panic runtimes.
The catch is monomorphised into the DLL at the `CLIO::effect*` call site, and a
force fault crosses as a value. The host's `call_effect_thunk` only forwards it.

**Allocator pairing.** The boxes are allocated by the DLL's Rust global
allocator and freed host-side. This holds because both sides use the default
system allocator. *Asserted, with a named falsifier:* a `#[global_allocator]` in the host binary or in any platform
DLL breaks the pairing.

**Consciously unprotected.** A hardware trap inside a capture destructor is not
recovered: the host's signal guard covers the force, and discharge runs during
teardown. Known captures are `i64`s and `CLOwned`, whose destructor is a host
reference decrement. *Trigger:* a platform whose captures own foreign resources
with destructors that can trap. That trigger returns the question to
`intrinsics`, which owns teardown and the guard.

### 4.3 Version discipline

`ABI_VERSION` is the single host↔DLL compatibility gate (Principle 14). None of
the `#[repr(C)]` or `#[repr(transparent)]` boundary types carries
`#[non_exhaustive]`: their absence is the signal that they are *layout*
contracts, not source contracts. A `#[non_exhaustive] #[repr(C)]` pair would
actively mislead, because the JIT-emitted code and the DLL read these structs by
hard-coded byte offsets — adding a field is source-compatible in Rust and
binary-breaking here.

The governing property, which the bump-rule enumeration in `ABI_VERSION`'s
rustdoc states:

> **A node layout is ABI-governed iff a DLL constructs or reads that node.**

So `Pure` and `Effect` are governed — `CLIO::*` builds them inside the DLL — and
`EffectPoll`/`Launch`/`Select` are not, because they are host-built and
host-interpreted and never cross the boundary. Adding those three tags was
correctly no bump; widening `Pure` is one, and so is changing what `Effect`'s
thunk word denotes (a repeatable borrowed thunk, ABI 11), because the layout
does not move but the pointer's contract does.

Mismatch is an unconditional load failure surfaced as
`PlatformError::AbiVersionMismatch` — the host refuses to call anything in an
ABI-mismatched DLL. The refusal is a safety property, not bookkeeping: a
stale-layout node read by a current host can produce a garbage word that the
teardown walker would call as a function pointer.

`platforms/shapes-badabi` is the standing refusal fixture. It hand-rolls its
manifest so it can bake a stale version, and by convention that version is the
one immediately preceding the current — a literal, never computed from the
const, since computing it would make the fixture track the host and stop being a
mismatch. **Re-pointing it is a standing obligation of every bump.**

### 4.4 Post-call stamps are tag-licensed

The host stamps a returned IO node after a platform call, and **the stamp is
selected by the returned node's tag, never by the callee's kind**: `IO_TAG_EFFECT`
takes the FQ fn-name pointer at base+40, `IO_TAG_PURE` takes the payload-glue word
at base+32 (valid at ABI ≥ 10 only), and any other tag takes no write at all.

The Pure arm is what closes the DLL's inability to name a glue address. The
backend knows the payload's concrete type from the platform entry's
`(Fn […] (IO T))` scheme — which invariant 8 guarantees is concrete — and adopts
the node at the crossing with the same canonical `drop<T>` every release site
calls. No second release identity is minted, and no DLL-minted `Pure` escapes the
seam, because `CLIO<T>` is not a `CLType` and therefore cannot be another node's
payload (§2).

Before S121 the fn-name stamp was selected by the call target's *kind* and stored
at base+40 unconditionally — an out-of-bounds heap write for any `Pure`-returning
platform fn, latent only because no shipped platform returns one. The rule of
record is `arch`'s (`design/arch/total-concreteness.md` §3.4, "the platform-return
seam"; register row R19 in `design/arch/safety-invariants.md` §4). This crate owns
the layout, the constant, the compile-time pin that fixes `HEAP_HEADER_SIZE +
IO_PURE_GLUE_OFFSET` at absolute byte 32, and the version gate that makes the
Pure arm's offset true — and owns no part of the emission. The backend owns its
independent absolute-offset pin and the tag-dispatched emission.

### 4.5 Tagged ADT heap layout

The one heap shape a DLL *asks the host to build* rather than building itself.
`CLAdt::<T>::construct` calls the `alloc_with_tag` host callback, which allocates
`HEAP_HEADER_SIZE + 8 + 8 × field_count` bytes, writes the header, writes the
variant tag as a `u32` at payload+0 (four bytes of pad follow, so fields stay
8-byte aligned), writes the `i64` fields from payload+8 upward, and returns the
**alloc base** pointer:

```
base + 0   [alloc_size: i64][rc: i64 = 1]   ; HeapHeader
base + 16  [tag: u32][pad: u32]             ; payload + 0
base + 24  [field_0: i64][field_1: i64] …   ; payload + 8, +16, …
```

Two properties are load-bearing, and both are asymmetries an author trips over:

- **`alloc_with_tag` returns the base; `alloc` returns the payload.** Every
  scalar, string and IO constructor subtracts the header size from what `alloc`
  hands back; `CLAdt::construct` passes `alloc_with_tag`'s result straight
  through. All heap `CL*` wrappers store base pointers, and `read_tag` /
  `read_field` add `HEAP_HEADER_SIZE` to reach the payload.
- **The tag is four bytes, the fields eight.** A field index is not a payload
  offset; the pad word is what keeps field 0 at payload+8.

The callback is wired to the `cranelisp-intrinsics` allocator by the host at DLL
load. Per-item truth — including the uninitialized-host fallback that panics
when a unit test constructs without a wired host — is the `HostCallbacks::
alloc_with_tag` rustdoc, which is this layout's canonical statement.

---

## 5. Bounded-context invariants

`design/arch/bounded-contexts.md` §5 is authoritative; the load-bearing ones for
a reader of this crate:

1. **Dispatch is GOT-indirect.** `got_slot = manifest index`. The macro emits the
   GOT as a const-init table populated by the linker; the host's `GotTable` wraps
   the dlsym'd table **in place, with no copy**. There is no per-entry function
   pointer, no name-based JIT dispatch, and no platform registry. Under the
   unified symbol lifecycle a platform effect is born
   `Concrete { slot: manifest-order mint, realization: Dll }`, so "slot *i* =
   descriptor *i*" is a mint-order invariant the load-boundary uniqueness scan
   surfaces.
2. **Stable C ABI**, governed by `ABI_VERSION` (§4.3).
3. **No closure-callback capability.** The boundary is **poll-in / wake-out**
   only. A cranelisp closure never crosses it; a continuation is the trampoline's
   own suspended state, not a handle a platform holds and calls. `HostCallbacks`
   carries exactly `alloc` and `alloc_with_tag` and **will not widen** — the
   earlier forward commitment to `rc_inc`/`rc_dec`/`invoke_closure` is retired
   (S98 user ruling). The residual case it was meant to serve — an un-invertible
   synchronous C dispatcher such as a comparator or a GUI loop — is handled one
   layer lower, with the callback written in the platform's own language and only
   a poll-shaped effect exposed.
4. **Marshalling tags shared with intrinsics** — one `i64` representation per
   `CLType`, agreed by this crate's documented layout, with the header size
   derived from `cranelisp_types::HeapHeader` rather than restated.
5. **`HostContext` initialised once per session**, by the host, with the callbacks
   valid for the session's lifetime.
6. **No DLL unloading mid-session.** This is what makes GOT slot pointers valid
   for the session, and what bounds the crate's deliberate leaks (the per-fn
   manifest allocations; the fault-cause bytes of a caught panic).
7. **Concurrency facts are declared by the DLL and consumed by the host.** The
   loader lifts the scheduling class and the poll-shape bit onto the callable;
   at runtime all permit scheduling flows through the trampoline-owned `HostCtx`
   vtable, never on values.
8. **A manifest signature is fully qualified and fully concrete.** A bare
   lowercase leaf parses as a type variable, and the load refuses with a located
   error naming the leaf and the function. A platform fn is a hand-written C-ABI
   body; a polymorphic platform signature is a declared contract nothing can
   check. The refusal lives at the load boundary (int), over the settlement
   funnel's structural check — **this crate adds no second predicate.**
9. **Post-call stamps are tag-licensed, and the DLL writes no glue.** Every store
   the host makes into a returned IO node is selected by that node's tag and is
   in-bounds for that tag's layout (§4.4). The DLL's only write to the `Pure`
   glue word is the `0` sentinel; the host adopts the node at the crossing. A
   DLL-side write of any other value is a second release mechanism, and a
   callback added to supply one would reopen invariant 3.
10. **Fault-guarded dispatch.** A platform-fn fault surfaces as a located
    `PlatformError::DispatchError { fn_name }`, never a process abort. Three
    coordinates: the fn-name travels *with* the Effect node (a thread-local
    cannot work — the node is forced far from where it was produced); the panic
    catch is DLL-local (§4.2); intrinsics captures the fault and int composes the
    diagnostic, keeping the runtime crate diagnostics-free.

### 5.1 No capability vocabulary

**The crate does not enumerate, match on, allow-list or otherwise know any
effect name, syscall or resource kind.** Effect names are data the DLL's manifest
supplies and `manifest_to_descriptors` copies; nothing in the crate branches on
one. `PollFn` carries an opaque state pointer and two host handles; `HostCtx`'s
readiness registration is fd-generic, so a socket, a pipe, an inotify fd and a
timerfd register identically; `ResourceRole` expresses a resource lifecycle
abstractly (`accept` is a `Produce`, `read`/`send` are `Consume`, a close is a
`Retire`) with no domain naming in the vocabulary.

The consequence is what makes the extension seam cheap: **there is no list a new
capability could be missing from**, so a platform capability nobody has written
yet costs the interface nothing. A future socket platform declares its handle
types as ordinary `.cl` modules and needs no platform-crate change — which
`exemplar/platforms/web` already demonstrates for a real `TcpListener`, `accept`,
`read` and `send`, entirely through the published facade.

Grade: **asserted with a named falsifier.** The falsifier is any `match`,
comparison or table lookup on an effect name, syscall name or resource kind
appearing inside this crate. It is stated rather than instrumented deliberately:
instrumenting it would require the manually maintained surface inventory this
document's conventions exclude.

The companion claim on the other side of the boundary — that the DLL never
writes a non-zero glue word (§4.1) — carries the same grade, with its falsifier
being any write to `IO_PURE_GLUE_OFFSET` in this crate or a `platforms/*` fixture
other than `CLIO::pure`'s `0` sentinel, or a third `HostCallbacks` field that
could supply one.

---

## 6. Schema and marker binding

Platforms **do not declare ADTs**. A platform's data types are ordinary `.cl`
modules, and its signatures reference them by fully-qualified name. A DLL that
marshals ADT values embeds the compiler-generated artifact via `include_str!`;
the macro parses it once into the per-DLL `Schema`, and field access resolves
`(offset, FieldType)` **by name**, callback-free — no host round trip per read.
Only construction touches host state, through `alloc_with_tag`.

Two independent gates, which compose and neither of which subsumes the other:

| Gate | Proves | When |
|---|---|---|
| **Layout hash** — the host regenerates the schema from its live tables and compares against the DLL's exported `__cranelisp_layout_hash_<name>` | the artifact is *current* | load / link. `--run` and `--link` refuse; the REPL warns and loads |
| **`adts:` name check** — a const scan of the same embedded bytes asserts each declared marker names an entry the artifact declares | marker names *agree* with the artifact | build |

Neither proves that a `read_field("…")` field-name string exists; field names
remain runtime strings. That residual is accepted, with its trigger recorded in
`adt-marker-binding.md` §"Residual: the field-name axis".

The marker mechanism, its two rejected alternatives, and why keeping explicit
impls is the more expensive option — a mismatch on the poll path is an
unattributable process abort, because poll frames carry no fault containment — is
`adt-marker-binding.md`.

---

## 7. Quality attributes

| Attribute | Assessment |
|---|---|
| **Simplicity** | Strong, and structurally bounded: the crate's purpose is "stable contract", so its complexity is capped by the C-ABI surface. Six modules, six concerns, no internal cadence, no second path for any operation. |
| **Maintainability** | Strong. One version gate protects layout; the dependency story is one crate, no `libloading`, no frontend. Blast radius for a change is the boundary itself, which is exactly where the version gate sits. |
| **Testability** (Principle 5) | Strong. Nothing in the crate requires a live DLL: `manifest_to_descriptors` takes a reference and returns owned data, the schema parser is a total function over `&str`, and the const scanners are pure. The `#[repr(C)]` layout pins make a field-order change conspicuous. |
| **Observability** | Adequate, and improving where it matters. Load and dispatch failures carry `PlatformError` with a location rather than a bare string. The remaining weak axis is field-name misses, which are runtime panics. |
| **Concurrency-safety** | The crate has no threads. Its invariants: the two allocator slots and the callbacks pointer are `AtomicPtr`/`SeqCst`; RC is `SeqCst` deliberately, because `Relaxed` is unsound here (a dec reordering before a field read is a read-after-free); DLL handles are session-global (invariant 6), which is what justifies the `unsafe impl Send + Sync` on `PlatformFn`. |
| **Performance** | `i64` passthrough where possible; only strings, ADTs and IO nodes allocate. An owned wrapper is one atomic increment on construct and one decrement on drop — the deliberate cost of RC compatibility with a concurrent runtime. |

---

## 8. Potential extensions, with triggers

Recorded so the next reader knows what was left out on purpose. None is
scheduled.

| Extension | Trigger |
|---|---|
| Compile-time field-name checking for `read_field` | a reported field-string mismatch, or a platform exceeding roughly a dozen distinct field names |
| Marker support for applied instantiation keys | the first production marker that needs one; today all are bare `module/Type` |
| A build-time concreteness check on manifest signatures | a second class of manifest-sig error surfacing only at load, or the load-time refusal's distance from the declaration proving to be the real cost |
| Removing `PlatformFn.ptr` (redundant with the GOT) | the next `ABI_VERSION` bump taken for another reason — a bump should have one cause, so the refusal evidence stays unambiguous |
| Renaming `inc_rc`/`dec_rc` to match the intrinsics spelling | a consumer cascade being paid for another reason |

---

## Cross-references

- `crates/cranelisp-platform/src/lib.rs` crate-root `//!` and per-item `///` —
  the public-API contract
- `crates/cranelisp-platform/CLAUDE.md` — the code's own voice: marshalling
  traps, layout invariants, the submodule seam map
- `design/arch/bounded-contexts.md` §5 — the bounded context and its invariants
- `design/arch/platform-interface.md` — the three-exports model, the generated
  schema, the v9 handle model
- `design/arch/total-concreteness.md` §3.4, §3.5 — the `Pure` glue word, the
  tag-dispatched platform-return stamp and the manifest-signature concreteness
  rule
- `design/arch/safety-invariants.md` §4 rows R19–R20 — IO-node stamp writes are
  tag-licensed, and an IO value is a reusable description of work
- `design/arch/interfaces.md` §"IO Tag Constants" — the node layouts of record
- `design/platform/platform-dlls.md` — authoring and loading mechanics
- `design/platform/poll-leaf-authoring.md` — the poll-shape leaf contract
- `design/platform/adt-marker-binding.md` — the marker mechanism decision
- `src/platform.rs` — the integration-side enactment of this contract
