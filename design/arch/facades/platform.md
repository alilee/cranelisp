# Facade spec — `crates/cranelisp-platform/`

**Bounded context citation.** Platform DLL loading, IO trampoline contract, and scheduling-class registry. Paired with `cranelisp-intrinsics` (Decision 43) — the IO trampoline lives in intrinsics; platform exposes the DLL ABI + host callbacks the trampoline uses. Exposes platform-fn registry to backend. See `bounded-contexts.md` §5 — Platform.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

The platform crate has two faces: a **host-side API** (what `int` and `cranelisp-intrinsics` use to load DLLs and dispatch effects — per Decision 43, intrinsics' IO trampoline reaches into platform via `HostContext` + the per-entry GOT slot — `ModuleEntry::Def.got_slot` indexes into `SymbolTable.got()`, which for `PrimitiveKind::PlatformEffect` entries holds the platform DLL fn address per Decision 26 (S66 amendment + rollback `1dc57ae` — GOT is the single source of truth for callable addresses; the briefly-considered sibling `fn_ptr` field was rolled back as redundant)) and a **DLL-author API** (what platform DLL authors use via the `declare_platform!` macro to register their fns and types). Both live in this crate.

### Marshaling — CL value wrappers (host + DLL)

The shared ABI between platform DLLs and runtime. Every Cranelisp value crosses the boundary as a CLType-wrapped i64.

```rust
pub trait CLType: Copy {
    fn to_raw(self) -> i64;                                                        // S67 W1 PFR — narrowed from {type_signature, from_repr, to_repr} to to_raw only.
                                                                                   // Rationale: host-side code never constructs a CL* from a raw i64 (DLL boundary
                                                                                   // hands them back as i64 and the host doesn't reverse the construction);
                                                                                   // `type_signature` would belong to the manifest, not the value wrapper, and the
                                                                                   // type-sig string lives on PlatformFn.type_sig (C-ABI string) and
                                                                                   // OwnedPlatformFnDescriptor.type_sig (owned Rust string) — both at the
                                                                                   // descriptor level, not the value level. `to_raw` (formerly `to_repr`) is
                                                                                   // sufficient for the lowering side of the boundary.
}

#[repr(transparent)] pub struct CLInt(i64);                                        // S67 W1 PFR — Principle 14 exemption: #[repr(transparent)] over i64 is the ABI.
#[repr(transparent)] pub struct CLString(i64);                                     // i64 = ptr to a HeapString allocation (layout owned by cranelisp-intrinsics per Decision 12 + 43).
#[repr(transparent)] pub struct CLBool(i64);                                       // 0 = false, 1 = true
#[repr(transparent)] pub struct CLFloat(i64);                                      // bit-cast f64

impl CLType for CLInt { fn to_raw(self) -> i64; }
impl CLType for CLString { fn to_raw(self) -> i64; }
impl CLType for CLBool { fn to_raw(self) -> i64; }
impl CLType for CLFloat { fn to_raw(self) -> i64; }

// Convenience conversions (all four primitive wrappers carry From-impls
// in both directions where they make sense; CLIO<CL> additionally carries
// From<CL>, From<i64> for CLInt's case, From<f64> for CLFloat, etc.):
impl From<i64> for CLInt;          impl From<CLInt> for i64;
impl From<bool> for CLBool;        impl From<CLBool> for bool;
impl From<f64> for CLFloat;        impl From<CLFloat> for f64;
impl From<&str> for CLString;      impl From<String> for CLString;
impl From<CLString> for String;
impl<CL: CLType> From<CLIO<CL>> for i64;
impl From<CLInt> for CLIO<CLInt>;     impl From<i64> for CLIO<CLInt>;
impl From<CLBool> for CLIO<CLBool>;   impl From<bool> for CLIO<CLBool>;
impl From<CLFloat> for CLIO<CLFloat>; impl From<f64> for CLIO<CLFloat>;
impl From<CLString> for CLIO<CLString>; impl From<String> for CLIO<CLString>;
impl From<CLInt> for CLIO<CLInt>;

#[repr(transparent)]
pub struct CLIO<CL: CLType>(i64, PhantomData<CL>);                                 // IO node — ptr to heap-allocated Pure | Effect | Bind | Par

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
    fn rc_inc(self);                                                               // calls intrinsics via HostCallbacks
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
    pub fn as_str(&self) -> &str;                                                  // borrow the intrinsics-owned bytes (HeapString lives in cranelisp-intrinsics per Decision 12 + Decision 43)
}
```

### Platform manifest and fn descriptor (DLL ABI — what every platform DLL exports)

```rust
#[repr(C)]
pub struct PlatformManifest {
    pub abi_version: u32,                                                          // must match cranelisp_platform::ABI_VERSION
    pub name: *const u8,                                                           // platform name (e.g. "stdio")
    pub name_len: usize,                                                           // S67 W1 PFR — length-prefixed (NOT null-terminated) because manifest crosses DLL boundary; null-terminator parsing would force the DLL author to guarantee null-termination across compiler/linker toolchains
    pub version: *const u8,                                                        // S67 W1 PFR — added: platform version string; surfaces in `manifest_to_descriptors` return tuple as the 2nd element
    pub version_len: usize,
    pub functions: *const PlatformFn,                                              // S67 W1 PFR — renamed from `fns` to match implementation; array of function descriptors
    pub function_count: usize,                                                     // S67 W1 PFR — renamed from `fn_count` to match implementation
}

#[repr(C)]
pub struct PlatformFn {
    pub name: *const u8,                                                           // kebab-case user-visible name (e.g. "print")
    pub name_len: usize,                                                           // S67 W1 PFR — length-prefixed alongside the pointer (rationale: same as PlatformManifest.name_len)
    pub jit_name: *const u8,                                                       // mangled JIT name per derive_jit_name (e.g. "cranelisp_print")
    pub jit_name_len: usize,                                                       // S67 W1 PFR
    pub ptr: *const u8,                                                            // fn pointer — type-erased (extern "C", all i64 params/returns)
    pub param_count: u32,                                                          // S67 W1 PFR — `u32` not `usize`; ABI is fixed-width across host/DLL pairs and `u32` is sufficient for any sane param count
    pub type_sig: *const u8,                                                       // type signature as S-expression string (e.g. "(Fn [String] (IO Int))")
    pub type_sig_len: usize,                                                       // S67 W1 PFR
    pub docstring: *const u8,                                                      // may be empty
    pub docstring_len: usize,                                                      // S67 W1 PFR
    pub param_names: *const *const u8,                                             // S67 W1 PFR — array of parameter name pointers (rationale: `/sig` / `/doc` REPL introspection surfaces named-parameter signatures; the DLL author writes the names in `declare_platform!` and they cross the boundary alongside the function pointer)
    pub param_name_lens: *const usize,                                             // S67 W1 PFR — parallel array of lengths
    pub param_name_count: usize,                                                   // S67 W1 PFR — count for both parallel arrays
    pub scheduling_class: u32,                                                     // S67 W1 PFR — `u32` discriminant (NOT `SchedulingClass` directly): the host re-interprets via `SchedulingClass::from(u32)`. Rationale: keep the C-ABI struct entirely free of Rust-typed fields so the DLL author's `cbindgen`-generated header is faithful. 0=Sequential, 1=Commutative, 2=ResourceSerial per Decision 26.
}

pub fn derive_jit_name(cl_name: &str) -> String;                                   // kebab-case → JIT mangled form
```

The `_len` fields throughout `PlatformFn` and `PlatformManifest` exist because length-prefixed strings (rather than null-terminated) avoid forcing every DLL author's toolchain to guarantee null-termination. The host reads `(ptr, len)` pairs and constructs UTF-8 slices via `std::slice::from_raw_parts` + `std::str::from_utf8`, which fails fast on malformed bytes. Any `_len` field change is a breaking change governed by `ABI_VERSION` per Principle 14.

Every platform DLL defines a static `PlatformManifest` and exports it via the `declare_platform!` macro (next section). The host (`cranelisp-platform::load_manifest`) reads the manifest and converts to safe `OwnedPlatformFnDescriptor` form.

### Host-side descriptors (safe Rust, post-load)

```rust
#[non_exhaustive]                                                                  // FIXME 0107 — currently missing in source; tracked as PIF for /dev (platform) Wave 2
pub struct OwnedPlatformFnDescriptor {
    pub name: String,
    pub jit_name: String,
    pub ptr: *const u8,
    pub param_count: usize,
    pub type_sig: String,
    pub docstring: String,
    pub param_names: Vec<String>,                                                  // S67 W1 PFR — added: owned form of the C-ABI parallel `param_names` / `param_name_lens` arrays. Surfaces in `/sig` and `/doc` introspection at the REPL.
    pub scheduling_class: SchedulingClass,                                         // owned form lifts the C-ABI `u32` to the typed enum via `SchedulingClass::from(u32)`
}

pub unsafe fn manifest_to_descriptors(
    manifest: &PlatformManifest,
) -> Result<(String, String, Vec<OwnedPlatformFnDescriptor>), PlatformError>;      // S67 W1 PFR — return tuple `(platform_name, platform_version, descriptors)`. The two leading strings come from `PlatformManifest.name` / `PlatformManifest.version` (each `(ptr, len)` pair lifted to an owned `String`); the descriptor vector comes from `PlatformManifest.functions`. `unsafe` because it dereferences the raw `PlatformFn` array.
```

`manifest_to_descriptors` is the public C-ABI → typed-Rust bridge: given a raw `PlatformManifest` (already located in a loaded DLL by the caller), it copies the descriptor list into safe Rust shapes and returns. Per BC §5, DLL lifecycle orchestration (`dlopen` + `libloading::Library` retention via `SharedState.kept_dlls`) is `int`'s job — the platform crate does not own DLL lifecycle. `int`'s session holds `Vec<OwnedPlatformFnDescriptor>` per loaded platform; the JIT registers each fn pointer via `JITBuilder::symbol` keyed by `jit_name`.

Per FIXME 0155 resolution — the historical `load_manifest(dll_path: &Path)` and `parse_type_sig(sig: &str)` entries are platform-internal `pub(crate)` helpers (called from `manifest_to_descriptors`). They are **not** part of the platform crate's public surface: out-of-tree DLL authors never call them, and `int` reaches the typed descriptors via `manifest_to_descriptors` only. The `load_manifest` entry point that opens the DLL with `libloading` lives in `int` per BC §5 — DLL lifecycle is integration-side. `parse_type_sig` similarly stays internal because type-signature parsing requires `cranelisp-typecheck` vocabulary access, which platform crate must not depend on (Principle 3).

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

Platform-fn invocation is via direct GOT lookup, NOT a centralised dispatch wrapper. The IO trampoline reads `got_slot` off the `ModuleEntry::Def` for the resolved `PrimitiveKind::PlatformEffect` entry per Decision 26 (S66 amendment + rollback `1dc57ae` — GOT is the single source of truth for callable addresses; the address is read via `symbol_table.got().load_slot(slot)`. The unified `fn_ptr` field briefly added in `b09ec76` was rolled back as redundant with the GOT — JIT-emitted code already reads addresses from `got_base + slot * 8`) and calls through it; `scheduling_class` is read from the same `PrimitiveKind::PlatformEffect` variant. Adding a `HostContext::dispatch` wrapper would re-introduce a parallel call path (Principle 7 violation) without buying anything the per-entry GOT slot doesn't already provide. (Per §2.13 — facade truth-telling; the implementation never built `dispatch`, and the post-Decision-26 architecture made it redundant.)

### Host callbacks — what platform DLL code can call back into runtime

```rust
#[repr(C)]
pub struct HostCallbacks {
    pub alloc: extern "C" fn(size: i64) -> i64,                                    // S67 W1 PFR — narrowed to alloc-only.
                                                                                   // Returns payload pointer (base + HEAP_HEADER_SIZE) as i64; size is the payload size, host adds the 16-byte heap header. Wires to `cranelisp_intrinsics::cranelisp_alloc` per Decision 43.
                                                                                   //
                                                                                   // The earlier facade text speculatively listed `dec` / `rc_inc` / `invoke_closure` to support
                                                                                   // Decision 31's "Callback support (forward commitment)" — i.e. when the spec adds `Fn a b` to the
                                                                                   // platform-ABI permitted-types list in §10.10.1, the DLL author needs to retain user-supplied
                                                                                   // closures across calls (rc_inc on store, rc_dec on release) and invoke them via the GOT
                                                                                   // (invoke_closure dispatches through the closure heap layout's code_ptr field).
                                                                                   //
                                                                                   // Status: DEFERRED to whenever `Fn a b` ABI lands. Not a current-facade deferral — the wider
                                                                                   // HostCallbacks shape is conditional on a future spec amendment. Per S67 Phase 2 verdict, the
                                                                                   // present-day implementation correctly exposes only `alloc`; bounded-context invariant 3
                                                                                   // below describes the Fn-a-b shape that will land alongside the spec amendment.
}
```

Platform DLL code currently uses `alloc` to allocate heap values (e.g. to produce a `CLString` result). When the `Fn a b` callback ABI lands, the struct widens to include `rc_inc`, `rc_dec`, and `invoke_closure` — see invariant 3 below for the durable contract. Per Decision 43, the underlying allocator and RC primitives live in `cranelisp-intrinsics`; `int` resolves the fn pointers at session init.

### Type signature parser — internal only

`parse_type_sig(sig: &str) -> Result<Vec<Type>, PlatformError>` is platform-internal `pub(crate)`, called from `manifest_to_descriptors` to lift each `PlatformFn.type_sig` into the resolved `Vec<Type>` form on `OwnedPlatformFnDescriptor.type_sig` (or the equivalent typed shape `int` needs for type-checking platform fn calls). Per FIXME 0155 resolution — not exposed to DLL authors or to `int` directly. The `int`-side type-checking entry point that `int` uses to validate platform fn calls lives in `int` per BC §5; it consumes the typed `Vec<Type>` already produced by `manifest_to_descriptors` rather than re-invoking the parser.

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
pub const HEAP_HEADER_SIZE: i64;                                                   // S67 W1 PFR — = HeapHeader::SIZE (16 bytes: total_size@+0 + rc@+8). Host allocator returns payload pointer = base + HEAP_HEADER_SIZE. DLL authors need this to compute payload pointers from base pointers in raw CLIO/CLString construction paths.
pub const STRING_HEADER_BYTES: usize;                                              // S67 W1 PFR — = 8 (i64 length prefix). String payload layout is [i64 len][u8 bytes…] starting at base + HEAP_HEADER_SIZE. Both consts exposed for DLL authors writing CLString builders that allocate via the host callback and lay out the payload by hand.
```

### Free functions

```rust
pub unsafe fn call_effect_thunk(thunk_ptr: i64) -> i64;                            // S67 W1 PFR — internal IO trampoline helper used by `CLIO::effect` and `CLIO::effect_on_resource` to invoke the boxed `FnOnce() -> CL` closure stored in the Effect node payload.
                                                                                   // Exposed because the IO trampoline (in cranelisp-intrinsics per Decision 43) calls back into platform to drive effect-node thunks; the function is `unsafe` because it takes ownership of the boxed closure via `Box::from_raw` and must be called exactly once per Effect node. Not a DLL-author API — DLL authors use `CLIO::effect{,_on_resource}` to build Effect nodes; the trampoline drives them.

pub fn derive_jit_name(cl_name: &str) -> String;                                   // kebab-case → JIT mangled form (named in §"Platform manifest and fn descriptor")
```

---

## Re-exports from `cranelisp-types` (external-audience exception per Principle 15)

```rust
pub use cranelisp_types::SchedulingClass;
pub use cranelisp_types::PlatformError;                                            // re-exported per Decision 42; surfaced via cranelisp-types so all crates can construct/match
```

Principle 15 forbids re-exports of `cranelisp-types` items from implementation-crate facades by default, but explicitly permits the **external-audience exception** for facades whose external consumers would not otherwise depend on `cranelisp-types`. `cranelisp-platform` qualifies: out-of-tree DLL author crates (`cranelisp-stdio`, `cranelisp-fs`, etc.) depend ONLY on `cranelisp-platform` and have no other reason to learn about `cranelisp-types`.

- `SchedulingClass` lives in `cranelisp-types` because `ModuleEntry::Def` carries it inside `PrimitiveKind::PlatformEffect { scheduling_class }` per Decision 26 (multi-consumer per Principle 15's heuristic — typecheck, backend, platform, intrinsics all reference it). Re-exported here for DLL authors.
- `PlatformError` lives in `cranelisp-types` per Decision 42 (`CranelispError::Platform(PlatformError)` is constructed by both platform and `int`'s error-formatting layer). Re-exported here for DLL authors who construct platform errors from their handler code.

No other re-exports.

---

## FQTypeName migration (Decision 47)

Per Decision 47 + `facades/types.md` §"FQTypeName migration plan (Sprint 67)", `cranelisp-platform` has **zero public-surface changes and zero in-crate hits** under the FQTypeName binding migration. Audit confirmed (Sprint 68 Phase 3, `/design (platform)`): grep for `TypeName` and `FQTypeName` across `crates/cranelisp-platform/src/*.rs` returns no matches, and `crates/cranelisp-platform/public-api.txt` carries no `TypeName` or `FQTypeName` references. No public type identifier crosses the platform boundary as a resolved-stage type identifier because the platform-DLL ABI uses S-expression type-signature strings (`PlatformFn.type_sig`) rather than resolved-stage type identifiers; resolution happens int-side, downstream of `manifest_to_descriptors`, where `int`'s `src/platform.rs::parse_io_type` constructs an `FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO"))` — that construction site is part of the **int** crate's accounting (alongside `exe.rs` / `pipeline.rs` IO-marker emission), not platform's. Migration disposition for `cranelisp-platform`: no-op; nothing to convert, nothing to keep with an exception comment.

## Consumed surface

The platform crate imports from:

- **`cranelisp-types`** — `SchedulingClass`, `Type` (for parse_type_sig output), `Span`, `CranelispError`, `Symbol`, `ModuleFullPath`, `PlatformSpec`.

The platform crate imports from no other workspace crate. (Per Decision 43, `cranelisp-intrinsics` is downstream of platform via the IO trampoline's per-entry GOT-slot dispatch — see §"Host context" for why no `HostContext::dispatch` wrapper exists. Platform does not name intrinsics; the host callbacks reach intrinsics via fn pointers installed at session init by `int`.)

External:
- **`libloading`** — for loading DLLs at runtime.

---

## Sealed traits

`CLType` and `CLHeap` are convention-sealed: only the four primitive wrappers (`CLInt`, `CLString`, `CLBool`, `CLFloat`) and `CLIO<T>` implement `CLType`; only `CLString` implements `CLHeap` (it is currently the only heap-typed wrapper). Platform DLL authors implement neither; they use the existing wrappers. The S67 W1 review confirmed there is no `mod sealed { pub trait Sealed {} }` super-bound in source — the `Copy` super-bound suffices in practice because DLL authors do not own any `Copy` type that could satisfy the i64 + ABI contract. Adding the `Sealed` super-bound is a candidate refinement; tracked as a future cleanup, not S67 scope.

```rust
pub trait CLType: Copy { fn to_raw(self) -> i64; }
pub trait CLHeap: CLType + Copy {
    fn rc_inc(&self);
    fn dec_rc(&self);                                                              // method name in source is `dec_rc` (not `rc_dec` — the asymmetry in spelling vs `rc_inc` is intentional, matching the historical name from `cranelisp-intrinsics`)
    fn raw_ptr(&self) -> i64;
    fn own(&self) -> CLOwned<Self>;                                                // non-consuming: takes &self, returns owning wrapper (does NOT consume the borrowed CLHeap)
    fn into_owned_consuming(self) -> CLOwned<Self>;                                // consuming: takes self by value
}
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

1. **Platform fn pointers live in `SymbolTable.got()`, indexed by `ModuleEntry::Def.got_slot`** (Decision 26, S66 amendment + rollback `1dc57ae` — GOT is the single source of truth for callable addresses). Per-DLL `OwnedPlatformFnDescriptor` is held on `int`'s `SharedState.kept_dlls`; at registration time `handle_platform` allocates a GOT slot for each platform-fn `ModuleEntry::Def` (with `kind: Primitive { primitive_kind: PlatformEffect { … } }` distinguishing the platform origin), records it as `got_slot: Some(slot)` on the entry, and writes the descriptor's pointer via `symbol_table.got().store_slot(slot, desc.ptr)`. The runtime lookup target is `entry_owning_module.got().load_slot(entry.got_slot.unwrap())`. `code` is `None` for platform entries — the DLL handle is the lifecycle owner, held in `kept_dlls`, not on the per-entry `code` field. `scheduling_class` lives inside the variant `PrimitiveKind::PlatformEffect { scheduling_class }` — making ill-formed states (a class on a non-platform entry) unrepresentable.

2. **Stable C ABI at the DLL boundary.** `PlatformManifest`, `PlatformFn`, `HostCallbacks` are `#[repr(C)]`. Layout changes require an `ABI_VERSION` bump. `load_manifest` validates the version on load and refuses mismatched DLLs with `PlatformError::AbiVersionMismatch`.

3. **Heap closures via GOT, not raw code pointers (Decision 31 callback support).** When `Fn a b` is added to spec §10.10.1 (currently future work), platform fn arguments of fn type pass as the heap closure address (Decision 11 layout: `[header | code_ptr | drop_glue_ptr | captures...]`), NOT raw code pointers. Platforms invoke retained closures via `HostCallbacks::invoke_closure` which dispatches through the GOT — so REPL redefinition retargets future invocations transparently. Retention requires `rc_inc` on storage, `rc_dec` on release.

4. **Marshaling tags shared with intrinsics.** The `CLType` impls use the same i64 layout the intrinsics helpers expect. `CLString.0` is a pointer to an intrinsics-allocated `HeapString` (Decision 12 — string layout owned by `cranelisp-intrinsics`; Decision 43 — intrinsics is the post-runtime-split host); `CLOwned<CLString>` participates in RC via `HostCallbacks.dec`. There is one i64 representation per CLType, agreed between platform and intrinsics via this crate's documented layout.

5. **`HostContext` initialised once per session.** `int` constructs `HostCallbacks` (with fn pointers into `cranelisp_intrinsics`) at `CompilerSession::new` and calls `HostContext::init` exactly once. Subsequent platform fn calls see the same callbacks for the session's lifetime.

6. **No DLL unloading mid-session.** Once a platform DLL is loaded via `load_manifest`, it stays loaded until session shutdown. This is what makes the per-symbol GOT-slot pointer valid for the session — DLL pages are not unmapped while symbols reference them.

7. **`scheduling_class` declared by the DLL, consumed by the IO trampoline.** Per Decision 26 — the IO trampoline reads `scheduling_class` off the destructured `PlatformEffect` variant when it dispatches an Effect, and uses it to decide whether to spawn the work on the IO thread pool, the CPU thread pool, etc. Platform authors choose the class statically per fn.
