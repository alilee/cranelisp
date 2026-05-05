# Facade spec — `crates/cranelisp-platform/`

**Bounded context citation.** Platform DLL loading, IO trampoline contract, and scheduling-class registry. Consumes runtime; exposes platform-fn registry to backend. See `bounded-contexts.md` §5 — Platform.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

The platform crate has two faces: a **host-side API** (what `int` and `cranelisp-runtime` use to load DLLs and dispatch effects) and a **DLL-author API** (what platform DLL authors use via the `declare_platform!` macro to register their fns and types). Both live in this crate.

### Marshaling — CL value wrappers (host + DLL)

The shared ABI between platform DLLs and runtime. Every Cranelisp value crosses the boundary as a CLType-wrapped i64.

```rust
pub trait CLType: Copy {
    fn type_signature() -> &'static str;
    fn from_repr(repr: i64) -> Self;
    fn to_repr(self) -> i64;
}

#[non_exhaustive] pub struct CLInt(pub i64);
#[non_exhaustive] pub struct CLString(pub i64);                                    // i64 = ptr to HeapString in runtime
#[non_exhaustive] pub struct CLBool(pub i64);                                      // 0 = false, 1 = true
#[non_exhaustive] pub struct CLFloat(pub i64);                                     // bit-cast f64

impl CLType for CLInt { /* … */ }
impl CLType for CLString { /* … */ }
impl CLType for CLBool { /* … */ }
impl CLType for CLFloat { /* … */ }

#[non_exhaustive]
pub struct CLIO<CL: CLType>(pub i64, PhantomData<CL>);                             // IO node — ptr to heap-allocated Pure | Effect | Bind | Par

impl<CL: CLType> CLIO<CL> {
    pub fn pure(val: CL) -> Self;                                                  // build a Pure node
    pub fn effect(f: impl FnOnce() -> CL + 'static) -> Self;                       // build an Effect node — closure stored in the heap node
    pub fn effect_on_resource(token: i64, f: impl FnOnce() -> CL + 'static) -> Self;  // Effect node tagged with a resource token (per spec §10 scheduling)
}
```

Per spec §10.10.1: the platform calling convention permits `Int`, `Bool`, `String`, `Float`, and `IO a` as argument and return types. `Fn a b` is reserved for future callback support per Decision 31's "Callback support (forward commitment)" sub-section.

### Heap-typed values crossed between platform and runtime

```rust
pub trait CLHeap: CLType + Copy {
    fn rc_inc(self);                                                               // calls runtime via HostCallbacks
    fn rc_dec(self);
    /* … */
}

#[non_exhaustive]
pub struct CLOwned<T: CLHeap> {
    inner: T,
}

impl<T: CLHeap> CLOwned<T> {
    pub fn new(val: T) -> Self;                                                    // takes ownership — drops invoke rc_dec via HostCallbacks
    pub fn into_inner(self) -> T;                                                  // release ownership without dec'ing
}

impl<T: CLHeap> Drop for CLOwned<T> { /* dec via HostCallbacks */ }
```

`CLOwned<T>` lets platform DLL code hold heap-typed Cranelisp values across multiple host-callback invocations with correct RC discipline. Each outer drop dec's via the host callback.

`CLString` accessor (host-side):

```rust
impl CLString {
    pub fn as_str(&self) -> &str;                                                  // borrow the runtime-owned bytes
}
```

### Platform manifest and fn descriptor (DLL ABI — what every platform DLL exports)

```rust
#[repr(C)]
pub struct PlatformManifest {
    pub name: *const u8,                                                           // null-terminated C string
    pub fns: *const PlatformFn,
    pub fn_count: usize,
    pub abi_version: u32,
}

#[repr(C)]
pub struct PlatformFn {
    pub name: *const u8,                                                           // null-terminated, kebab-case (the user-visible name)
    pub jit_name: *const u8,                                                       // mangled JIT name per derive_jit_name
    pub ptr: *const u8,                                                            // fn pointer — type-erased
    pub param_count: usize,
    pub type_sig: *const u8,                                                       // null-terminated type signature string
    pub docstring: *const u8,                                                      // null-terminated, may be empty
    pub scheduling_class: SchedulingClass,                                         // per Decision 26 — platform fns declare their scheduling class
}

pub fn derive_jit_name(cl_name: &str) -> String;                                   // kebab-case → JIT mangled form
```

Every platform DLL defines a static `PlatformManifest` and exports it via the `declare_platform!` macro (next section). The host (`cranelisp-platform::load_manifest`) reads the manifest and converts to safe `OwnedPlatformFnDescriptor` form.

### Host-side descriptors (safe Rust, post-load)

```rust
#[non_exhaustive]
pub struct OwnedPlatformFnDescriptor {
    pub name: String,
    pub jit_name: String,
    pub ptr: *const u8,
    pub param_count: usize,
    pub type_sig: String,
    pub docstring: String,
    pub scheduling_class: SchedulingClass,
}

pub fn load_manifest(dll_path: &Path) -> Result<Vec<OwnedPlatformFnDescriptor>, PlatformError> †;
```

`load_manifest` opens the DLL via `libloading`, locates the exported `__cranelisp_platform_manifest` symbol, copies the descriptor list into safe Rust shapes, and returns. `int`'s session holds `Vec<OwnedPlatformFnDescriptor>` per loaded platform; the JIT registers each fn pointer via `JITBuilder::symbol` keyed by `jit_name`.

### Host context — runtime ↔ platform bridge

```rust
pub struct HostContext {
    callbacks: AtomicPtr<HostCallbacks>,
}

impl HostContext {
    pub const fn new() -> Self;
    pub unsafe fn init(&self, callbacks: *const HostCallbacks);                    // called once per session by int
}
```

Platform-fn invocation is via direct GOT lookup, NOT a centralised dispatch wrapper. The IO trampoline reads `platform_fn_ptr` off the `ModuleEntry::Def` for the resolved `PrimitiveKind::PlatformEffect` entry per Decision 26 and calls through it; `scheduling_class` is read from the same variant. Adding a `HostContext::dispatch` wrapper would re-introduce a parallel call path (Principle 7 violation) without buying anything the per-entry pointer doesn't already provide. (Per §2.13 — facade truth-telling; the implementation never built `dispatch`, and the post-Decision-26 architecture made it redundant.)

### Host callbacks — what platform DLL code can call back into runtime

```rust
#[repr(C)]
pub struct HostCallbacks {
    pub alloc: extern "C" fn(size: usize) -> *mut u8,                              // → cranelisp_runtime::heap_alloc
    pub dec: extern "C" fn(ptr: *mut u8),                                          // → cranelisp_runtime RC dec (debug helper)
    pub rc_inc: extern "C" fn(ptr: *mut u8),                                       // → atomic_rmw via runtime helper
    pub invoke_closure: extern "C" fn(closure_ptr: *mut u8, args: *const i64, n_args: usize) -> i64,  // GOT-indirect dispatch through closure's code_ptr (Decision 31 callback support)
    /* … */
}
```

Platform DLL code uses these callbacks to allocate heap values (e.g., to produce a `CLString` result), to retain user-supplied closures across calls, to invoke retained closures. Each callback's behaviour is documented as part of the platform ABI (`bounded-contexts.md` §5 references `spec/10-io.md §10.10.3`).

### Type signature parser (used by load_manifest + by `int` for type checking platform fn calls)

```rust
pub fn parse_type_sig(sig: &str) -> Result<Vec<Type>, PlatformError>;              // "Int -> IO Bool" → [Type::Int, Type::IO(Box::new(Type::Bool))]
```

### `declare_platform!` macro (DLL-author API)

```rust
#[macro_export]
macro_rules! declare_platform {
    (
        name: $name:literal,
        host: $host:ident,
        fns: { $($fn_name:literal => $fn_pointer:expr),* $(,)? }
    ) => { /* generates the PlatformManifest static + extern symbol */ };
}
```

Every platform DLL invokes `declare_platform!` once. The macro emits the static `PlatformManifest`, the exported `__cranelisp_platform_manifest` symbol, and registers each fn against the host context.

### Errors

`PlatformError` is hosted in `cranelisp-types` per Decision 42 — coordinates as data via `ErrorLocation` carriers per variant. Re-exported here for caller convenience. See `facades/types.md` §"Errors and warnings" for the canonical definition.

```rust
pub use cranelisp_types::PlatformError;
// = LoadFailed { dll: PathBuf, cause: String, location: ErrorLocation }
// | ManifestNotFound { dll: PathBuf, location: ErrorLocation }
// | AbiVersionMismatch { dll: PathBuf, expected: u32, found: u32, location: ErrorLocation }
// | DispatchError { fn_name: Symbol, cause: String, location: ErrorLocation }
// (#[non_exhaustive])
```

Platform-origin failures construct `PlatformError` and surface via `CranelispError::Platform(PlatformError)`; int's `Sess::format_error` consumes through Decision 39's mode-conditional source-resolution path. The `(platform "name")` form's span flows into the `location` field so a missing DLL produces `lib/main.cl:42:7: error: platform "stdio" not found in search path` rather than a free-floating string.

### Public consts

```rust
pub const ABI_VERSION: u32;                                                        // platform ABI version — bumped on breaking changes
pub const IO_TAG_PURE: i64;                                                        // IO node tag — Pure (spec §10)
pub const IO_TAG_EFFECT: i64;                                                      // IO node tag — Effect (spec §10)
pub const IO_TAG_BIND: i64;                                                        // IO node tag — Bind (spec §10)
pub const IO_TAG_PAR: i64;                                                         // IO node tag — Par (spec §10.12)
pub const IO_EFFECT_RESOURCE_OFFSET: i64;                                          // byte offset of resource token in Effect node payload
```

---

## Re-exports from `cranelisp-types` (external-audience exception per Principle 15)

```rust
pub use cranelisp_types::SchedulingClass;
pub use cranelisp_types::PlatformError;                                            // re-exported per Decision 42; surfaced via cranelisp-types so all crates can construct/match
```

Principle 15 forbids re-exports of `cranelisp-types` items from implementation-crate facades by default, but explicitly permits the **external-audience exception** for facades whose external consumers would not otherwise depend on `cranelisp-types`. `cranelisp-platform` qualifies: out-of-tree DLL author crates (`cranelisp-stdio`, `cranelisp-fs`, etc.) depend ONLY on `cranelisp-platform` and have no other reason to learn about `cranelisp-types`.

- `SchedulingClass` lives in `cranelisp-types` because `ModuleEntry::Def` carries it inside `PrimitiveKind::PlatformEffect { scheduling_class }` per Decision 26 (multi-consumer per Principle 15's heuristic — typecheck, backend, platform, runtime all reference it). Re-exported here for DLL authors.
- `PlatformError` lives in `cranelisp-types` per Decision 42 (`CranelispError::Platform(PlatformError)` is constructed by both platform and `int`'s error-formatting layer). Re-exported here for DLL authors who construct platform errors from their handler code.

No other re-exports.

---

## Consumed surface

The platform crate imports from:

- **`cranelisp-types`** — `SchedulingClass`, `Type` (for parse_type_sig output), `Span`, `CranelispError`, `Symbol`, `ModuleFullPath`, `PlatformSpec`.

The platform crate imports from no other workspace crate. (Runtime is downstream of platform via the IO trampoline's call to `HostContext::dispatch`, but platform does not name runtime — the host callbacks reach runtime via fn pointers installed at session init.)

External:
- **`libloading`** — for loading DLLs at runtime.

---

## Sealed traits

`CLType` is the sealed trait — only the four primitive wrappers (`CLInt`, `CLString`, `CLBool`, `CLFloat`) and `CLIO<T>` may implement it from inside this crate. `CLHeap` is sealed via `CLType` super-bound (since `CLType` is sealed, `CLHeap` is too). Platform DLL authors implement neither; they use the existing wrappers.

```rust
mod sealed { pub trait Sealed {} }
pub trait CLType: sealed::Sealed + Copy { /* … */ }
```

---

## `#[non_exhaustive]` DTOs

Per Principle 14 — FFI boundary types are governed by layout discipline (`ABI_VERSION`), not source-level evolution guards. `#[non_exhaustive]` applies to public DTOs EXCEPT those carrying `#[repr(C)]` or `#[repr(transparent)]`:

**Exempt (layout contracts; governed by `ABI_VERSION`):**
- `#[repr(C)]`: `PlatformManifest`, `PlatformFn`, `HostCallbacks` — read by the platform-DLL loader and the IO trampoline via hard-coded byte offsets. Any field change is a breaking change requiring an `ABI_VERSION` bump (gated by `load_manifest`'s version check) and a coordinated `declare_platform!` macro contract update.
- `#[repr(transparent)]`: `CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<T>`, `CLOwned<T>` — read by JIT-emitted code as raw `i64`. The wrapper's underlying type IS the ABI; an underlying-type swap is breaking and `#[non_exhaustive]` would not catch it. Direct construction (`CLInt(42)`) is preserved as part of the DLL-author API surface.

**Carry `#[non_exhaustive]`:**
- `OwnedPlatformFnDescriptor` — plain Rust struct (post-load owned form, not crossing the DLL ABI). The standard facade convention applies.
- `PlatformError` — re-exported from `cranelisp-types` per Decision 42; `#[non_exhaustive]` set there.

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-platform` makes with the rest of the workspace:

1. **Platform fn pointers live on `ModuleEntry::Def.platform_fn_ptr`** (Decision 26). Per-DLL `OwnedPlatformFnDescriptor` is held on `int`'s `SharedState.kept_dlls`; the per-symbol `platform_fn_ptr` field on the corresponding `ModuleEntry::Def` is the runtime lookup target. `scheduling_class` lives inside the variant `PrimitiveKind::PlatformEffect { scheduling_class }` — making ill-formed states (a class on a non-platform entry) unrepresentable.

2. **Stable C ABI at the DLL boundary.** `PlatformManifest`, `PlatformFn`, `HostCallbacks` are `#[repr(C)]`. Layout changes require an `ABI_VERSION` bump. `load_manifest` validates the version on load and refuses mismatched DLLs with `PlatformError::AbiVersionMismatch`.

3. **Heap closures via GOT, not raw code pointers (Decision 31 callback support).** When `Fn a b` is added to spec §10.10.1 (currently future work), platform fn arguments of fn type pass as the heap closure address (Decision 11 layout: `[header | code_ptr | drop_glue_ptr | captures...]`), NOT raw code pointers. Platforms invoke retained closures via `HostCallbacks::invoke_closure` which dispatches through the GOT — so REPL redefinition retargets future invocations transparently. Retention requires `rc_inc` on storage, `rc_dec` on release.

4. **Marshaling tags shared with runtime.** The `CLType` impls use the same i64 layout the runtime helpers expect. `CLString.0` is a pointer to a runtime-allocated `HeapString`; `CLOwned<CLString>` participates in RC via `HostCallbacks.dec`. There is one i64 representation per CLType, agreed between platform and runtime via this crate's documented layout.

5. **`HostContext` initialised once per session.** `int` constructs `HostCallbacks` (with fn pointers into `cranelisp_runtime`) at `CompilerSession::new` and calls `HostContext::init` exactly once. Subsequent platform fn calls see the same callbacks for the session's lifetime.

6. **No DLL unloading mid-session.** Once a platform DLL is loaded via `load_manifest`, it stays loaded until session shutdown. This is what makes the per-symbol `platform_fn_ptr` valid for the session — DLL pages are not unmapped while symbols reference them.

7. **`scheduling_class` declared by the DLL, consumed by the IO trampoline.** Per Decision 26 — the IO trampoline reads `scheduling_class` off the destructured `PlatformEffect` variant when it dispatches an Effect, and uses it to decide whether to spawn the work on the IO thread pool, the CPU thread pool, etc. Platform authors choose the class statically per fn.
