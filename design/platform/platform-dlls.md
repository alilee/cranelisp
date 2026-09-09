# Platform DLLs — authoring and loading mechanics

Subordinate to `platform.md`, which carries the crate's shape and its
invariants. This document carries the *mechanics*: the manifest, the wrapper
types and the capture-RC protocol a DLL author works in, the discovery and load
sequence, the error conditions, and the reference platforms.

Canonical per-item truth is the source rustdoc. Where a constant or a constructor
signature appears here, it is illustrative of the shape; the source is
authoritative.

## Architectural context

Platform DLLs are how a Cranelisp program performs side effects. The IO model
(`spec/10-io.md`) defines IO as a deferred task tree; platform DLLs supply the
leaf nodes that do work when the trampoline forces them.

The crate DAG for platform work:

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

`cranelisp-platform` is the shared ABI contract crate: both the host binary and
every platform DLL depend on it. It holds type definitions, wrapper types, the
schema parser and the `declare_platform!` macro, and has no runtime behaviour of
its own. It depends only on `cranelisp-types` — notably not on `libloading`,
which is int-side.

## C-ABI Contract

### ABI Version

The bump trail is canonical in the `ABI_VERSION` rustdoc; the current stamp is
**10** (the `Pure` payload-glue word). The host checks
`manifest.abi_version == ABI_VERSION` at load and refuses a mismatch with
`PlatformError::AbiVersionMismatch`. A refused DLL contributes nothing: the host
calls no function in it.

**What obliges a bump** is stated as a property rather than a list, in
`platform.md` §4.3: any field added, removed, reordered or retyped in a
`#[repr(C)]` boundary struct; any change to a constant a DLL reads by hard-coded
offset; and any layout change to **a node a DLL constructs or reads** — which is
`Pure` and `Effect`, not the host-built `EffectPoll`/`Launch`/`Select`.

Two historical append-in-place changes did **not** bump, correctly: the fn-name
and capacity fields were appended to the `Effect` node while no out-of-tree DLL
had shipped against the then-current stamp, so host and DLLs rebuilt together.
**That latitude ends the moment a platform ships externally against a stamp**,
and it never applied to a change that moves an existing offset.

`platforms/shapes-badabi` is the standing refusal fixture — it hand-rolls its
manifest so it can bake a stale version, by convention the one immediately
preceding the current. Re-pointing it is a standing obligation of every bump.

### IO Tag Constants

Shared between platform DLLs and the host trampoline:

| Constant | Value | Node type |
|----------|-------|-----------|
| `IO_TAG_PURE` | 0 | Completed value. Payload 24 bytes: `[tag, payload, payload_glue]`, the glue at `IO_PURE_GLUE_OFFSET`. A DLL writes the `0` sentinel there — it cannot name a host `drop<T>` address, and must not try; the host adopts the node with the real glue when it returns across the ABI (`platform.md` §4.1, §4.4) |
| `IO_TAG_EFFECT` | 1 | Deferred effect (opaque closure) |
| `IO_TAG_BIND` | 2 | Chain (internal) |
| `IO_TAG_PAR` | 3 | Automatic IO scheduling (spec §10.12) |
| `IO_TAG_EFFECT_POLL` | 4 | Poll-shape async leaf (core/ungated since v8; backend-built state-closure node, io-trampoline §12) |
| `IO_TAG_LAUNCH` | 5 | Launch-and-continue (S96 Chunk B; host-built/host-interpreted, never crosses the DLL ABI) |
| `IO_TAG_SELECT` | 6 | Race/select combinator (S96 Chunk C; host-built/host-interpreted, never crosses the DLL ABI) |

Tags 4–6 are **host-built and host-interpreted**: they never cross the DLL
boundary, which is why adding them was no bump. `IO_TAG_EFFECT_POLL` in
particular is a backend-built state-closure node, not a DLL allocation — the
poll-leaf author receives it as an opaque `state` pointer. See
`design/backend/io-trampoline.md` §12 and `poll-leaf-authoring.md`.

### `PlatformManifest`

Returned by the DLL's entry point function `cranelisp_platform_manifest`. Contains metadata and an array of function descriptors.

```rust
#[repr(C)]
pub struct PlatformManifest {
    pub abi_version: u32,           // Must match host's ABI_VERSION
    pub name: *const u8,           // Platform name (e.g. "stdio")
    pub name_len: usize,
    pub version: *const u8,        // Platform version string
    pub version_len: usize,
    pub functions: *const PlatformFn,  // Array of function descriptors
    pub function_count: usize,
}
```

All string fields use raw `*const u8` + `usize` length pairs for C compatibility. The manifest and its contents must remain valid for the process lifetime (the `declare_platform!` macro achieves this via leaked `Box` allocations).

### `PlatformFn`

Describes a single platform function:

```rust
#[repr(C)]
pub struct PlatformFn {
    pub name: *const u8,              // Cranelisp name (e.g. "print")
    pub name_len: usize,
    pub jit_name: *const u8,          // JIT symbol name (e.g. "cranelisp_print")
    pub jit_name_len: usize,
    pub ptr: *const u8,               // Function pointer (extern "C")
    pub param_count: u32,             // Number of i64 parameters
    pub type_sig: *const u8,          // Type as S-expression (e.g. "(Fn [String] (IO Int))")
    pub type_sig_len: usize,
    pub docstring: *const u8,         // Human-readable description
    pub docstring_len: usize,
    pub param_names: *const *const u8,  // Array of parameter name pointers
    pub param_name_lens: *const usize,  // Parallel array of lengths
    pub param_name_count: usize,
    pub scheduling_class: u32,        // SchedulingClass discriminant
}
```

The `type_sig` field carries the full type signature as an S-expression string. The host parses this to register the function in the type system. This keeps type information in the manifest without requiring the platform crate to depend on the typechecker's `Type` enum.

The `jit_name` is derived from the Cranelisp name by the `derive_jit_name()` function: prepend `cranelisp_` and replace `-` with `_`. For example, `read-line` becomes `cranelisp_read_line`.

### `HostCallbacks`

Callbacks provided by the host to the platform at manifest time:

```rust
#[repr(C)]
pub struct HostCallbacks {
    pub alloc: extern "C" fn(i64) -> i64,
}
```

The `alloc` callback allocates heap memory through the runtime allocator in
`cranelisp-intrinsics`. **The two callbacks do not agree on what they return**,
and this is the crate's sharpest marshalling trap: `alloc` returns the **payload**
pointer (base + header), so every scalar/string/IO constructor subtracts the
header size to recover the base before storing it, while `alloc_with_tag` returns
the **base** already and `CLAdt::construct` passes it straight through. All heap
`CL*` wrappers store base pointers. The crate's own `CLAUDE.md` carries the
citation-level detail.

**Why only `alloc`?** Deallocation is handled by the RC system (when RC reaches zero). Platform code never explicitly frees Cranelisp heap values. The `alloc` callback is the only host service platforms need.

### `SchedulingClass`

Controls how the IO scheduler (future Ring 4 sprint) treats effects from this function:

```rust
#[repr(u32)]
pub enum SchedulingClass {
    Sequential = 0,       // Ordered relative to other effects
    Commutative = 1,      // Freely reorderable
    ResourceSerial = 2,   // Parallel across different resource tokens
}
```

All Sprint 16 platform functions use `Sequential`. Including `Commutative` and `ResourceSerial` in the ABI from the start avoids a version bump when auto-scheduling lands.

Default is `Sequential` (safe fallback for unknown values).

## Safe Wrapper Types

Platform authors work with safe `CL*` wrapper types instead of raw `i64`. All `unsafe` is encapsulated in the `cranelisp-platform` crate.

| Type | Wraps | Conversion |
|------|-------|------------|
| `CLInt` | `i64` | Direct passthrough |
| `CLBool` | `i64` | `0 = false`, `1 = true` |
| `CLFloat` | `i64` | IEEE 754 f64 bitcast |
| `CLString` | `i64` | Pointer to `[i64 len][u8 bytes...]` payload |

### `CLString`

`CLString` wraps a pointer to heap-allocated string data. The pointer points to the payload (after the 16-byte heap header: `alloc_size` + `rc`). Layout at the pointer:

```
ptr -> [len: i64][bytes: u8...]
       offset 0   offset 8
```

`CLString::as_str()` reads the length and returns a `&str` over the byte data. `CLString::from(&str)` allocates via the host allocator and copies bytes.

### `CLIO<CL>`

Generic IO-wrapped return type. Platform functions return `CLIO<CLInt>`, `CLIO<CLString>`, etc.

Two construction methods:

```rust
impl<CL: CLType> CLIO<CL> {
    /// Wrap a completed value in a Pure node (tag=0).
    pub fn pure(val: CL) -> Self;

    /// Wrap a closure in an Effect node (tag=1).
    /// The closure is double-boxed to produce a thin pointer.
    pub fn effect(f: impl FnOnce() -> CL + 'static) -> Self;

    /// Effect with a resource token (for ResourceSerial scheduling).
    /// Lowers to `effect_on_resource_with_capacity(token, 1, f)`.
    pub fn effect_on_resource(token: i64, f: impl FnOnce() -> CL + 'static) -> Self;

    /// Effect with a resource token AND a capacity (S95 slice-3 carrier).
    /// The trampoline runs a `Semaphore(capacity)` per token: `token` effects
    /// overlap up to `capacity`, the (capacity+1)th parks (arch §8.1; the pool
    /// lives intrinsics-side, reactor.md §2.8). `capacity` rides the node at
    /// `IO_EFFECT_CAPACITY_OFFSET` (32). Capacity is per-RESOURCE (per-token),
    /// platform-supplied dynamically at the effect site — not a static field.
    pub fn effect_on_resource_with_capacity(token: i64, capacity: i64, f: impl FnOnce() -> CL + 'static) -> Self;
}
```

`CLIO::pure(val)` allocates a 3-field node `[tag=0, value, payload_glue]` (24
bytes of payload) on the host heap. The glue word is written as the `0`
sentinel and that is the **only** value a DLL may write there: it is an initial
value, replaced by the host's tag-dispatched adoption stamp when the node
crosses back as a platform call's return value (`platform.md` §4.1, §4.4). A DLL
cannot name a host `drop<T>` address and must not try. The DLL and this crate do
not implement the post-publication claim: after adoption, intrinsics alone
atomically exchanges the word to `Claimed`, observing the prior `Scalar`,
`Claimed` or `Owned(glue)` state as force and teardown contend for the one
payload obligation.

`CLIO::effect(f)` double-boxes the closure and allocates an `IO_TAG_EFFECT`
node, whose payload is **40 bytes**: `[tag, thunk_ptr, resource_token, fn_name,
capacity]` at payload offsets 0/8/16/24/32. Two of those the constructor does
not fill in with a meaningful value:

- **`fn_name`** is reserved **null** by the DLL, which cannot know the
  cranelisp-level name, and is stamped by the host after the call returns — under
  the tag licence of `platform.md` §4.4, so the store lands only on a node whose
  tag says it has that field. An unstamped node degrades to `"<unknown>"` in a
  dispatch diagnostic, never a crash.
- **`capacity`** is `1` for `effect`/`effect_on_resource` — today's
  serial-within-token — and is supplied explicitly by
  `effect_on_resource_with_capacity`, the additive sibling.

Every widening of this node has been **append-only**; no existing offset has ever
moved, and that is the discipline to preserve. The double-boxing produces a thin
pointer (one `i64`) from a trait object (two). The trampoline calls
`call_effect_thunk` to reclaim ownership and invoke the closure **exactly once**
— single-shot by contract — returning an `EffectOutcome` under the DLL-local
fault catch (`platform.md` §4.2).

### `call_effect_thunk`

```rust
pub unsafe fn call_effect_thunk(thunk_ptr: i64) -> i64;
```

Reclaims the double-boxed closure via `Box::from_raw` and invokes it. This **consumes** the thunk -- it is valid to call exactly once. The trampoline must not force the same Effect node twice.

### `CLType` Trait

Marker trait providing `to_raw(self) -> i64` for conversion to the ABI-level
representation, so a raw `i64` cannot be accidentally lifted into `CLIO`.
Conventionally sealed: the four primitive wrappers and `CLAdt<T>` implement it,
and **`CLIO<T>` deliberately does not** — which is what makes `pure(pure(…))`
unconstructable, so no IO node can be hidden inside another node's payload
(`platform.md` §2, §4.4).

## Capture-RC Protocol

**This is a critical correctness requirement.** Platform functions that capture heap values (particularly `CLString`) across effect thunk boundaries MUST use `CLOwned<CLString>` to maintain correct reference counts.

### The Problem

A platform function receives a `CLString` parameter. When it returns a `CLIO::effect(closure)`, the closure captures the string. But the closure executes **later**, when the trampoline forces the Effect node. By that time, the original caller may have dropped its reference to the string, decrementing its RC to zero and freeing the memory. The closure would then read freed memory.

### The Solution: `CLOwned<T>`

```rust
pub trait CLHeap: CLType + Copy {
    fn raw_ptr(&self) -> i64;
    fn inc_rc(&self);      // Atomic increment of RC header
    fn dec_rc(&self);      // Atomic decrement; frees if RC reaches 0
    fn own(&self) -> CLOwned<Self>;
}

pub struct CLOwned<T: CLHeap> {
    inner: T,
}

impl<T: CLHeap> CLOwned<T> {
    pub fn new(val: T) -> Self {
        val.inc_rc();   // +1 on creation
        CLOwned { inner: val }
    }
}

impl<T: CLHeap> Drop for CLOwned<T> {
    fn drop(&mut self) {
        self.inner.dec_rc();  // -1 on drop
    }
}

impl<T: CLHeap> Deref for CLOwned<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.inner }
}
```

`CLString` implements `CLHeap`. The RC header is at `ptr - 8` (one i64 before the payload pointer). `inc_rc` and `dec_rc` use atomic operations (`AtomicI64::fetch_add`/`fetch_sub` with `Ordering::SeqCst`), matching the backend's Cranelift `atomic_rmw` semantics (arch decision 13). Note: `Ordering::Relaxed` for dec is unsound — it allows the dec to be reordered before reads of object fields, potentially reading freed memory.

### Usage Pattern

```rust
pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
    let owned = s.own();   // inc RC — string now has an extra reference
    CLIO::effect(move || {
        // `owned` is moved into the closure. When the trampoline
        // forces this Effect, the closure executes:
        println!("{}", owned.as_str());
        // When `owned` is dropped (closure returns), RC is decremented.
        CLInt::from(0i64)
    })
}
```

**Rule**: If a platform function captures a `CLString` (or any `CLHeap` type) in an `effect` closure, it MUST call `.own()` and capture the `CLOwned` handle, not the bare `CLString`. Capturing a bare `CLString` is a use-after-free bug.

Functions that do NOT capture heap values (e.g., `read-line` which takes no parameters) do not need `CLOwned`.

### Why Not Automatic?

The `CLString` copy in the function signature is a raw pointer copy with no RC semantics. Making `CLString` automatically inc-on-copy would require a `Clone` impl with side effects, which is error-prone and would inc on every parameter pass (including non-capturing paths). The explicit `.own()` call documents the intent and ensures RC management only happens when needed.

## `HostContext`

Each platform DLL has a static `HostContext` instance that stores the host callbacks:

```rust
pub struct HostContext {
    callbacks: AtomicPtr<HostCallbacks>,
}
```

`HostContext::init(callbacks)` is called by the `declare_platform!` macro during manifest generation. It:
1. Copies the `HostCallbacks` struct to a leaked `Box` (process-lifetime storage)
2. Stores the `alloc` function pointer in a crate-global `GLOBAL_ALLOC` static

Each DLL gets its own copy of `GLOBAL_ALLOC` (separate compilation unit). This is correct -- each DLL's `CLString::from()` allocates via the host allocator, not its own. `HostContext::init()` must be called per DLL, which the `declare_platform!` macro guarantees.

## `declare_platform!` Macro

The macro generates the DLL entry point and handles all boilerplate:

```rust
declare_platform! {
    name: "stdio",
    version: "0.1.0",
    host: HOST,
    functions: [
        print_string {
            cl_name: "print",
            sig: "(Fn [String] (IO Int))",
            doc: "Print a string followed by a newline",
            params: [s],
            scheduling: SchedulingClass::Sequential,
        },
        read_line {
            cl_name: "read-line",
            sig: "(Fn [] (IO String))",
            doc: "Read a line from stdin",
            params: [],
            scheduling: SchedulingClass::Sequential,
        },
    ]
}
```

The macro generates an `extern "C" fn cranelisp_platform_manifest(callbacks) -> PlatformManifest` function that:

1. Calls `HOST.init(callbacks)` to initialize host callbacks and set the global allocator
2. Captures each function pointer and parameter metadata
3. Derives JIT symbol names from Cranelisp names (`derive_jit_name`)
4. Builds a leaked `PlatformFn` array with 'static lifetime
5. Returns a `PlatformManifest` struct

All string data uses static string literals (`.as_ptr()` on `&str`) or leaked heap allocations. The manifest's entire contents are valid for the process lifetime.

**Platform authors define `extern "C"` functions outside the macro.** The macro only handles registration. This keeps the function implementations clean and testable independently.

## `cranelisp-stdio` Design

The reference platform providing standard console IO. Crate type: `cdylib`.

### `print` — `(Fn [String] (IO Int))`

Takes a Cranelisp string, returns an IO effect that writes the string followed by a newline to stdout. Returns `0` as the inner value.

```rust
#[unsafe(export_name = "cranelisp_print")]
pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
    let owned = s.own();  // Capture-RC: inc RC for deferred use
    CLIO::effect(move || {
        println!("{}", owned.as_str());
        CLInt::from(0i64)
    })
}
```

Key details:
- Uses `println!` (adds newline), matching spec 10.9.2: "print a string followed by a newline"
- Returns `IO Int` with value 0, matching spec 10.9.2 signature
- Scheduling class: `Sequential` -- print output must appear in program order
- Uses `CLOwned` capture-RC protocol for the string parameter

### `read-line` — `(Fn [] (IO String))`

Reads a line from stdin, trims trailing newline/carriage return, returns the result as a Cranelisp string.

```rust
#[unsafe(export_name = "cranelisp_read_line")]
pub extern "C" fn read_line() -> CLIO<CLString> {
    CLIO::effect(move || {
        let mut buf = String::new();
        std::io::stdin().read_line(&mut buf).unwrap_or(0);
        buf.trim_end_matches(&['\n', '\r'][..]).to_string().into()
    })
}
```

Key details:
- No parameters, so no capture-RC needed
- `CLString::from(String)` allocates via the host allocator inside the closure (host context is already initialized)
- Scheduling class: `Sequential` -- reads must occur in order (stdin is a serial resource)
- On read failure, `unwrap_or(0)` produces an empty string

## Test-leaf platforms (`test-capture`, `pool-demo`)

Two in-tree test platforms exercise the ABI without touching real IO. **`cranelisp-test-capture`** (below) substitutes in-memory buffers for stdio. **`platforms/pool-demo`** (S95) is the capacity-carrier test leaf: `pool-read`/`pool-write`/`pool-log`, all declaring `(token, capacity)` via `CLIO::effect_on_resource_with_capacity` on **blocking** effects — the fixture that proved capacity-N pool sizing, first-writer-wins reconciliation, and parking on the blocking carrier (the poll-shape leaves are `platforms/poll-pool` and `platforms/async-demo` — see `poll-leaf-authoring.md`). All are workspace members rebuilt with the compiler.

## `cranelisp-test-capture` — the general-purpose behavioural fixture

The in-tree platform that substitutes in-memory buffers for stdio, and the one
in-tree platform whose declared functions exist to be *observed* rather than to
do work. `print` appends to a captured buffer instead of stdout and `read-line`
pops a pre-configured queue, so its signatures make it a drop-in for
`cranelisp-stdio`; beyond that pair it carries effects across all three
scheduling classes and, from ABI 10, the `Pure`-returning pair that gives the
platform-return adoption stamp (`platform.md` §4.4) its only in-tree traffic.

The declared set is the manifest in `platforms/test-capture/src/lib.rs`; it is not
enumerated here, because a fixture's function list is exactly the kind of census
that decays. What belongs here is the *shape*: a behavioural fixture grows a
function when a boundary needs observing, and the additions are appended so no
existing manifest index — and therefore no GOT slot — moves.

### Test Utility Functions

Exported from the cdylib for direct use by Rust test code via `libloading`. These are NOT registered as platform functions (not in the manifest).

| Function | Purpose |
|----------|---------|
| `test_capture_set_input(lines, lens, count)` | Queue input lines for `read-line` |
| `test_capture_get_output(out_ptr, out_len)` | Retrieve all captured print output |
| `test_capture_free_output(ptr, len)` | Free buffer from `get_output` |
| `test_capture_reset()` | Clear both input queue and output buffer |

### State Management

Uses `Mutex`-protected `Vec<String>` (output) and `VecDeque<String>` (input) as process-global state. The `Mutex` provides thread safety, and poison recovery handles panics in `#[should_panic]` tests.

### Rejected alternative: subprocess capture only

Testing IO purely by running `cranelisp --run` as a subprocess and diffing stdout
needs no extra crate, and it is still how some e2e lanes work. It was rejected as
the *only* mechanism because it cannot drive `read-line` without piping stdin,
cannot assert on individual effects, and — decisively — gives no way to exercise
an ABI shape that produces no output at all, which is what the `Pure`-returning
pair is for.

## DLL Loading

The runtime loads platform DLLs via `libloading` (Rust wrapper around `dlopen`/`dlsym`).

### Loading Sequence

When the host encounters a `(platform stdio)` declaration:

1. **Resolve path**: `resolve_platform_path("stdio")` searches the platform search path (see below) for the DLL file.

2. **Open library**: `libloading::Library::new(path)` calls `dlopen` to load the shared library into the process.

3. **Get manifest function**: `lib.get(b"cranelisp_platform_manifest")` calls `dlsym` to find the entry point. The function has signature `extern "C" fn(*const HostCallbacks) -> PlatformManifest`.

4. **Call manifest**: Construct a `HostCallbacks { alloc: runtime::alloc_with_rc }` and pass it to the manifest function. This initializes the DLL's host context and returns the manifest.

5. **Check ABI version**: `manifest.abi_version == ABI_VERSION`. Reject with error on mismatch.

6. **Extract descriptors**: `manifest_to_descriptors(&manifest)` converts C-ABI raw pointers to safe Rust `OwnedPlatformFnDescriptor` structs.

7. **Register with JIT**: For each descriptor, insert `(jit_name, fn_ptr)` into the JIT's dynamic symbol table. Declare the function on the JIT module with the correct signature (derived from `param_count`).

8. **Register with typechecker**: Parse each function's `type_sig` S-expression to produce a `Type`, and register it in the `platform.<name>` module (e.g., `platform.stdio`) as a `DefKind::Primitive { primitive_kind: PlatformEffect }`.

9. **Keep library alive**: Push the `Library` handle into a `Vec<Library>` on the JIT. The library must remain loaded for the process lifetime (function pointers point into its code segment).

### Manifest Name Validation

After loading, the host validates that the manifest's `name` field matches the declared platform name. For `(platform stdio)`, the manifest must report `name: "stdio"`. A mismatch is a compile-time error -- it means the wrong DLL was loaded.

### Error Conditions

| Condition | Error |
|-----------|-------|
| Platform DLL not found | `"platform 'foo' not found"` |
| `dlopen` failure | `"failed to load platform library: ..."` |
| Missing manifest function | `"platform missing manifest function: ..."` |
| ABI version mismatch | `"platform ABI version mismatch: platform has N, host expects M"` |
| Invalid UTF-8 in manifest | `"invalid UTF-8 in platform name/function/..."` |
| Manifest name != declared name | `"platform manifest name 'X' does not match declared name 'Y'"` |

## Platform Search Path

Three-tier search with environment variable override. First match wins.

### Search Order

1. **`CRANELISP_PLATFORM_PATH`** (env var, if set): Colon-separated list of directories. Each directory is searched for the DLL file. This provides explicit control for deployment and CI environments.

2. **`./platforms/`**: Relative to the project root (the `project_root` used by the REPL session, or the working directory for batch mode). Looks for `<name>.<ext>` (e.g., `stdio.dylib`).

3. **Cargo build output**: `target/debug/lib<crate_name>.<ext>` then `target/release/lib<crate_name>.<ext>`. Development convenience only -- when platform DLLs are built as workspace members, their output lands here. The crate name is derived from the platform name: `cranelisp-<name>` with hyphens replaced by underscores (e.g., `libcranelisp_stdio.dylib`).

4. **`~/.cranelisp/platforms/`**: User-global install location. For platforms installed system-wide.

### DLL Filename Convention

The filename depends on the search tier:

- Tiers 1, 2, 4: `<name>.<ext>` (e.g., `stdio.dylib`)
- Tier 3 (Cargo output): `lib<crate_name>.<ext>` (e.g., `libcranelisp_stdio.dylib`)

Platform extension by OS:

| OS | Extension |
|----|-----------|
| macOS | `.dylib` |
| Linux | `.so` |
| Windows | `.dll` |

### Explicit Path Bypass

If the platform name contains `/`, `\`, or ends with `.dylib`/`.so`/`.dll`, it is treated as a filesystem path and used directly, bypassing the search order. This handles cases like `(platform "./my-platform.dylib")`.

## Integration with the Module System

When `(platform stdio)` is encountered in the entry module:

1. The platform DLL is loaded and its functions are registered.
2. A synthetic module `platform.stdio` is created in the module table.
3. Each platform function is registered as `ModuleEntry::Def { kind: DefKind::Primitive { primitive_kind: PlatformEffect, ... } }`.
4. Other modules access platform functions via `(import [platform.stdio [print read-line]])` or `(import [platform.stdio [*]])`.
5. Only the entry module may contain a `(platform ...)` declaration (spec 10.9.1).

## Rejected Alternatives

### Trait-based platform interface

Considered defining a Rust trait `Platform` with methods for each IO operation. Rejected because:
- Trait objects (`dyn Platform`) add vtable indirection
- The C-ABI contract is more portable (works with non-Rust platform implementations)
- The manifest approach carries metadata (types, docs, scheduling) that traits cannot express
- The sketch's C-ABI approach works well in practice

### Embedded platform (no DLL)

Considered linking `print`/`read-line` directly into the binary. Rejected because:
- Violates the spec's platform abstraction model (spec 10.9)
- Makes test-capture substitution impossible
- The DLL approach is the production design, not interim architecture (Principle 8)

### Function-level `dlsym` (no manifest)

Considered looking up each platform function individually via `dlsym`. Rejected because:
- No metadata (types, docs, scheduling class) available at the ABI level
- No ABI version checking
- No validation that the DLL actually provides the expected functions

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

The prototype compiler this document originally cited was deleted at the close
of Sprint 87; its sources are recoverable from git history and are not a live
reference.
