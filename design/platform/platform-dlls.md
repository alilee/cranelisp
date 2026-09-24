# Platform DLLs — authoring and loading mechanics

Subordinate to `platform.md`, which carries the crate's shape and its
invariants. This document carries the *mechanics*: what a DLL author works in,
what the host does with the result, and why each mechanism is the one chosen.

Canonical per-item truth is the source rustdoc. Struct fields, constructor
signatures and constant values are named here only where a shape is being
explained; the source is authoritative and this document does not mirror it.

## Architectural context

Platform DLLs are how a Cranelisp program performs side effects. The IO model
(`spec/10-io.md`) defines IO as a deferred task tree; platform DLLs supply the
leaf nodes that do work when the trampoline forces them.

```
cranelisp (binary) ─┬─> cranelisp-backend ──> cranelisp-intrinsics
                    │                         cranelisp-primitives
                    │                              │
                    │                              v
                    │                          cranelisp-types
                    │                              ^
                    │                              │
                    └─> cranelisp-platform <───────┘

platforms/*/            ──> cranelisp-platform
exemplar/platforms/web/ ──> cranelisp-platform
```

Both the host binary and every platform DLL depend on `cranelisp-platform`; that
is its purpose. It depends only on `cranelisp-types` — notably not on
`libloading`, which is int-side, and not on the typechecker.

---

## 1. The version gate

The host checks `manifest.abi_version == ABI_VERSION` before it calls anything,
and refuses a mismatch with `PlatformError::AbiVersionMismatch`. A refused DLL
contributes nothing.

**What obliges a bump** is stated as a property, not a list, in `platform.md`
§4.3: any field added, removed, reordered or retyped in a `#[repr(C)]` boundary
struct; any change to a constant a DLL reads by hard-coded offset; and any layout
change to **a node a DLL constructs or reads** — `Pure` and `Effect`, not the
host-built `EffectPoll`/`Launch`/`Select`. The bump trail itself is canonical in
the `ABI_VERSION` rustdoc.

Two historical append-in-place widenings of the `Effect` node did **not** bump,
correctly: no out-of-tree DLL had shipped against the then-current stamp, so host
and DLLs rebuilt together. **That latitude ends the moment a platform ships
externally against a stamp**, and it never applied to a change that moves an
existing offset.

`platforms/shapes-badabi` is the standing refusal fixture. It hand-rolls its
manifest so it can bake a stale version — by convention the one immediately
preceding the current, as a literal rather than a computation, since computing it
would make the fixture track the host and stop being a mismatch. **Re-pointing it
is a standing obligation of every bump.**

---

## 2. The C-ABI contract types

Four `#[repr(C)]` types carry the boundary, all governed by `ABI_VERSION`:

| Type | Carries |
|---|---|
| `PlatformManifest` | the platform's name, version, ABI stamp and its array of function descriptors |
| `PlatformFn` | one function: its cranelisp name, its JIT symbol name, its fully-qualified type signature, parameter names, docstring and scheduling facts |
| `HostCallbacks` | the two host services a DLL may call — `alloc` and `alloc_with_tag` — and permanently no more (`platform.md` §5, invariant 3) |
| `EffectOutcome` | a forced thunk's result, or the fault a DLL-local panic catch converted into a value |

Strings ride as raw pointer + length pairs for C compatibility. The manifest and
everything it points at must stay valid for the process lifetime, which
`declare_platform!` achieves with leaked allocations — bounded by the no-unload
invariant (`platform.md` §5, invariant 6).

`jit_name` is derived from the cranelisp name mechanically: prepend `cranelisp_`
and replace `-` with `_`, so `read-line` becomes `cranelisp_read_line`.

**`type_sig` is a string, deliberately.** Carrying the signature as an
S-expression rather than a structured type is what keeps this crate free of a
dependency on the typechecker's vocabulary; the host parses it. Every signature
must be fully qualified and fully concrete, and the load refuses one that is not
(`platform.md` §5, invariant 8).

### Scheduling facts

A function declares either a `SchedulingClass` — `Sequential`, `Commutative` or
`ResourceSerial` — or, for a poll-shape leaf, a `ConcurrencyDescriptor` carrying
the token, capacity, the blocking bit and a `ResourceRole`. The host lifts these
onto the callable at load; at runtime every scheduling decision flows through the
trampoline-owned `HostCtx` vtable, never on a value. What a role obliges a leaf
author to do is `poll-leaf-authoring.md` §3.

### The marshalling trap

**The two callbacks do not agree on what they return.** `alloc` returns the
**payload** pointer, so every scalar, string and IO constructor subtracts the
header size to recover the base; `alloc_with_tag` returns the **base** already
and `CLAdt::construct` passes it through (`platform.md` §4.5). All heap `CL*`
wrappers store base pointers. This is the crate's sharpest trap, and the crate's
own `CLAUDE.md` carries the citation-level detail.

**Why only these two?** Deallocation belongs to the RC system; platform code
never explicitly frees a cranelisp heap value. Nothing else the boundary needs is
a host service — and widening the pair is how a closure-callback capability would
re-enter, which invariant 3 forbids.

---

## 3. Safe wrapper types

An author works in `CL*` wrappers rather than raw `i64`; all `unsafe` is
encapsulated in this crate.

| Type | Represents | Notes |
|---|---|---|
| `CLInt` | `i64` | direct passthrough |
| `CLBool` | `0` / `1` | |
| `CLFloat` | `f64` bit pattern | |
| `CLString` | base pointer to `[header][len: i64][bytes…]` | RC-participating |
| `CLAdt<T>` | base pointer to a tagged allocation (`platform.md` §4.5) | RC-participating; `T` is the marker |
| `CLIO<T>` | base pointer to a heap IO node | **not** a `CLType` |

`CLType` is sealed by convention, and `CLIO<T>`'s exclusion from it is
load-bearing rather than an oversight: it is what makes `pure(pure(…))`
unconstructable through the facade, so no IO node can hide inside another node's
payload and every DLL-minted node reaches the host as a platform call's return
value (`platform.md` §2, §4.4).

### Constructing an IO node

`CLIO::pure(value)` builds a `Pure` node and writes the `0` sentinel into the
payload-glue word. That sentinel is the **only** value a DLL may write there: a
DLL cannot name a host `drop<T>` address and must not try, and the host adopts
the node with the real glue when it crosses back (`platform.md` §4.1, §4.4). The
DLL implements no part of the force or teardown rule.

The `effect` family builds an `Effect` node around a double-boxed closure — the
double box is what produces a thin pointer from a trait object. Two of that
node's fields the constructor does not fill with a meaningful value:

- **`fn_name`** is left null, because the DLL cannot know the cranelisp-level
  name. The host stamps it after the call under the tag licence of `platform.md`
  §4.4, and an unstamped node degrades to `"<unknown>"` in a dispatch diagnostic
  rather than crashing.
- **`capacity`** defaults to serial-within-token and is supplied explicitly by
  the capacity-carrying sibling constructor.

The closure is **repeatable**: `call_effect_thunk` borrows it, and forcing a
node again runs it again, possibly concurrently from two `Par` branches. It
must therefore be `Fn() -> CL + Send + Sync + 'static`. It lives as long as
the node, and `drop_effect_thunk` drops it and its captures once, when the host
frees the node. `platform.md` §4.2 records the ownership and the DLL-local
fault catch on both paths. For an author, this means:

- A closure that consumes a capture must clone it on each call.
- `Rc`, `RefCell` and `Cell` captures become `Arc`, `Mutex` or atomics.
- A closure's side effect happens once per force, not once per node.

---

## 4. The capture-RC protocol

**This is a correctness requirement, not a convention.**

A platform function is an extern, so it owns every heap parameter: the caller
has transferred the reference
([bounded contexts](../arch/bounded-contexts.md) §4b invariant 6). The function
releases each parameter it does not return; the per-parameter fates are
[RC discipline](../backend/ring2-rc.md) §3.3.

An effect closure runs *later*, when the node is forced, so a parameter it reads
must keep its reference until the node is freed. `CLHeap::into_owned_consuming(self)`
moves the transferred reference into a `CLOwned<T>` without incrementing; the
closure captures the `CLOwned`, which releases the reference when the node, and
with it the closure, is dropped. The shipped `platforms/stdio` `print_string`:

```rust
pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
    let owned = s.into_owned_consuming(); // the transferred reference; no +1
    CLIO::effect(move || {                // `owned` releases it when the node is freed
        println!("{}", owned.as_str());
        CLInt::from(0i64)
    })
}
```

`CLHeap::own(&self)` increments, so its `CLOwned` holds a reference of its own.
It is correct only for a reference the function does not own, such as a heap
field read out of a borrowed structure (`CLAdt::own_field`). On a transferred
parameter it leaks one reference per call. There is deliberately no
`into_inner`: an owned reference leaves only by being dropped or by being handed
on as a value.

**Rule:** a closure captures a transferred heap parameter only as the
`CLOwned` from `into_owned_consuming`. A bare `CLHeap` capture holds no
reference: released at return, the closure reads freed memory; never released,
it leaks. A function that captures nothing, such as the parameterless
`read-line`, needs no owned handle.

**Grade.** The two helpers' RC effects are measured by the
`into_owned_consuming`/`own` contrast tests and the balanced capture-effect test
in `crates/cranelisp-platform/src/tests.rs`. Each function's choice between them
is *asserted*: `own()` on a transferred parameter compiles. Candidate falsifier:
an M3 alloc/free parity run ([diagnostic modes](../intrinsics/diagnostic-modes.md)
§3) over a program that calls a capturing platform function repeatedly, showing
allocations exceeding deallocations by the call count.

**Rejected: `own()` plus an explicit release before return.** It balances, but
only while every author remembers the release; `into_owned_consuming` makes the
release part of the capture.

RC operations are `SeqCst`, matching the backend's Cranelift `atomic_rmw`
semantics. `Relaxed` on the decrement is unsound here: it permits the decrement
to be reordered before a field read, which is a read-after-free.

**Why not automatic?** The `CLString` copy in a function signature is a raw
pointer copy with no RC semantics. An inc-on-copy `Clone` would fire on every
parameter pass including non-capturing ones, and would put a side effect behind
an implicit operation. The explicit call documents the intent and pays only where
the risk exists.

---

## 5. `HostContext` and `declare_platform!`

Each DLL has one static `HostContext` holding the host callbacks. The macro's
generated entry point initialises it before anything else, which is what makes
the per-DLL allocator slots valid. Each loaded DLL gets its own copy of those
slots because it is a separate compilation unit — and that is correct: every
DLL's allocation goes through the *host* allocator, not its own.

`declare_platform!` emits the three exports the boundary needs — the manifest
entry point, the GOT slab and, where a schema is embedded, the layout hash — from
one declaration. It has two arms, with and without an embedded schema; the
schema arm additionally accepts the `adts:` marker key (`adt-marker-binding.md`).
The macro's own rustdoc is the authority on its keys.

Two shapes are deliberate:

- **Author functions live outside the macro.** It handles registration only, so
  implementations stay ordinary `extern "C"` functions that are readable and
  testable on their own.
- **One macro invocation per DLL, emitting everything.** Folding the schema
  embed, the marker emission and the marker/schema agreement check into the call
  every DLL already makes exactly once is what makes the check unforgettable.

---

## 6. Reference and fixture platforms

| Platform | What it is for |
|---|---|
| `platforms/stdio` | the reference console platform: a blocking `print` and a poll-shape `read-line` in one manifest — the mixed-shape witness |
| `platforms/test-capture` | the general-purpose behavioural fixture: buffers substituted for stdio, effects across all three scheduling classes, and the `Pure`-returning pair that gives the platform-return adoption stamp its only in-tree traffic |
| `platforms/shapes` | the reference ADT platform — one marker, read on a blocking thunk |
| `platforms/shapes-badabi` | the standing ABI-refusal fixture (§1); hand-rolled manifest, never dispatched |
| `platforms/pool-demo` | the capacity carrier on **blocking** effects: pool sizing, first-writer-wins reconciliation, parking |
| `platforms/async-demo`, `platforms/poll-pool` | the poll-shape leaves — see `poll-leaf-authoring.md` §7 |
| `exemplar/platforms/web` | the full shape: typed handles, `Produce`/`Consume` leaves, an embedded schema |

A fixture's declared function list is not enumerated here; that is exactly the
kind of census that decays silently. What belongs here is the shape: a
behavioural fixture grows a function when a boundary needs observing, and
additions are **appended**, so no existing manifest index — and therefore no GOT
slot — moves.

`test-capture` also exports a handful of utility functions for direct use by Rust
test code. They are deliberately *not* in the manifest: they are test-harness
controls, not platform effects, and putting them in the manifest would make them
callable from cranelisp source.

**Rejected alternative: subprocess capture only.** Running `cranelisp --run` and
diffing stdout needs no extra crate, and some e2e lanes still work that way. It
was rejected as the *only* mechanism because it cannot drive an input-consuming
effect without piping stdin, cannot assert on an individual effect, and —
decisively — gives no way to exercise an ABI shape that produces no output at
all, which is what the `Pure`-returning pair exists for.

---

## 7. Loading

The host loads platform DLLs through `libloading`. The sequence, on a
`(platform <name>)` declaration in the entry module:

1. **Resolve** the DLL path (§8).
2. **`dlopen`** the library and **`dlsym`** the manifest entry point.
3. **Call the entry point**, handing it the `HostCallbacks` wired to the
   `cranelisp-intrinsics` allocator. This initialises the DLL's host context and
   returns its manifest.
4. **Check the ABI version** and refuse a mismatch before anything else is read.
5. **Lift the descriptors** — `manifest_to_descriptors` UTF-8-validates the raw
   pointers into owned Rust values.
6. **Register a synthetic `platform.<name>` module**, one entry per function,
   each born concrete with a manifest-order slot and a DLL realization. The
   module's `GotTable` **wraps the DLL's exported GOT slab in place, with no
   copy**; dispatch is GOT-indirect and there is no name-based JIT dispatch and
   no platform registry (`platform.md` §5, invariant 1).
7. **Retain the library handle** for the session. The no-unload invariant is what
   makes the wrapped slab's pointers valid for the session's lifetime.

Where a schema is embedded, the host also regenerates the schema from its live
tables and compares the canonical layout hash against the DLL's exported one:
`--run` and `--link` refuse a mismatch, the REPL warns and loads
(`platform.md` §6).

Failures are `PlatformError` values carrying a location, not bare strings:
`LoadFailed`, `ManifestNotFound`, `AbiVersionMismatch`, `LayoutHashMismatch`, and
at dispatch time `DispatchError`. The variants and their payloads are
`cranelisp-types`' to define.

Only the entry module may carry a `(platform …)` declaration (spec §10.9.1).
Other modules reach the effects by importing `platform.<name>`.

---

## 8. Finding the DLL

If the name looks like a filesystem path — it contains a separator or ends in a
platform library extension — it is used directly and no search happens.

Otherwise three tiers are searched in order, first match winning:

1. `platforms/` under the project root;
2. `platforms/` under each configured library directory;
3. each extra platform directory supplied by configuration or environment.

Every tier tries two filename conventions: the plain `<name>.<ext>`, and Cargo's
`libcranelisp_<name>.<ext>` with hyphens replaced by underscores. The second is
what lets a workspace-member platform be found straight out of the build
directory during development. The extension is the host OS's — `.dylib`, `.so`
or `.dll`.

---

## 9. Rejected alternatives

**A Rust `Platform` trait.** Trait objects add vtable indirection, a Rust trait
cannot be implemented by a non-Rust platform, and — decisively — a trait cannot
carry the metadata the manifest does: type signatures, docstrings, parameter
names and scheduling facts. The C ABI is the portable contract.

**Linking the reference effects into the binary.** It would violate the spec's
platform abstraction, and it would make fixture substitution impossible. The DLL
path is the production design, not interim architecture.

**Per-function `dlsym` with no manifest.** No metadata at the ABI level, no
version check, and no way to validate that the DLL provides what was expected.

---

## References

- `design/platform/platform.md` — the master design: the crate's shape, its ABI
  and node layouts, and its bounded-context invariants
- `design/platform/poll-leaf-authoring.md` — the poll-shape leaf contract
- `design/platform/adt-marker-binding.md` — the marker-binding mechanism
- `crates/cranelisp-platform/CLAUDE.md` — the code's own voice: marshalling
  traps, layout invariants, the submodule seam map
- `design/arch/bounded-contexts.md` §5 — the platform bounded context
- `design/arch/platform-interface.md` — the three-exports model and the
  generated schema
- `design/arch/interfaces.md` — `PlatformEffect`, `PlatformDecl`, the IO tag
  constants
- `spec/10-io.md`, `spec/12-runtime.md` — the IO model and runtime value
  representation
- `src/platform.rs` — the integration-side load, path resolution and
  type-signature parsing
