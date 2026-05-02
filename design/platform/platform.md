# Platform — Master Design

`crates/cranelisp-platform/` — the shared interface contract between the cranelisp host binary and platform DLLs. Both sides depend on this crate; that is its purpose. It owns the C-ABI types, the safe wrappers presenting those types in Rust, the layout constants both sides must agree on, the macro DLLs use to publish their manifests, and the marshalling helpers that keep RC discipline correct across the DLL boundary.

This is the master design doc per `/design`'s charter. Subordinate topic docs in `design/platform/` are listed in §11 and cited by section.

> **Note (no audit yet).** Unlike frontend/backend/typecheck/int, no `audits/platform-*.md` exists. §3 is derived from direct reading of `crates/cranelisp-platform/src/lib.rs` (940 lines, single file). Audit pass is tracked by FIXME 0101 — sequenced after Decision 40 / FIXME 0103 lands so the runtime + platform audits look at post-relocation shape.

---

## 1. Bounded-context recap

Per `design/arch/bounded-contexts.md` §5 — platform is the *shared interface contract crate*. It exposes the C-ABI types, the wrappers, the layout constants, and the manifest macro. It owns no runtime state and no cadence.

**Owns**:
- ABI value wrappers — `CLType` trait, `CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<T>`, `CLOwned<T>`, `CLHeap` trait
- C-ABI manifest types — `PlatformManifest`, `PlatformFn`, `HostCallbacks` (all `#[repr(C)]`)
- Manifest parsing — `manifest_to_descriptors()` → `OwnedPlatformFnDescriptor`
- Effect-thunk consumption primitive — `call_effect_thunk` (single-shot, called from runtime)
- Constants — `ABI_VERSION`, `IO_TAG_PURE`/`IO_TAG_EFFECT`/`IO_TAG_BIND`/`IO_TAG_PAR`, `HEAP_HEADER_SIZE`, `IO_EFFECT_RESOURCE_OFFSET`, `STRING_HEADER_BYTES`
- DLL author macro — `declare_platform!`
- Per-DLL global allocator handle — `HostContext`, `GLOBAL_ALLOC` static
- JIT name derivation — `derive_jit_name()` (kebab → `cranelisp_<snake>`)

**Does not own**:
- DLL lifecycle storage — `SharedState.kept_dlls: DashMap<PathBuf, Arc<DllHandle>>` lives in `int`. Path search, `dlopen`, ABI version validation, and lifecycle orchestration also live in `int` (`src/platform.rs::load_platform_dll`, `resolve_platform_path`).
- IO trampoline — owned by `cranelisp-runtime`. Platform exposes `call_effect_thunk` and the IO node tag layout; runtime reduces the tree.
- `IoObserver` callback contract — owned by `cranelisp-runtime` per Decision 40. Platform DLLs do not register observers; runtime does.
- Scheduling decisions — `int`'s scheduler reads `scheduling_class` off `PrimitiveKind::PlatformEffect` to choose threadpool/serialisation.
- Platform fn pointer storage at runtime — lives on `ModuleEntry::Def.platform_fn_ptr` per Decision 26.
- Type signature parsing — `parse_type_sig` lives in `int` (`src/platform.rs`), invoked at platform-load time after `manifest_to_descriptors` returns the raw string.
- Per-DLL platform implementations — separate downstream crates (e.g., `platforms/stdio/`).
- Spec for IO semantics — `/spec` (`spec/10-io.md`).

**Crosses the boundary outward**: C-ABI types, wrappers, constants, and the macro — to both host and DLL consumers. **Inward**: `SchedulingClass`, `HeapHeader` from `cranelisp-types`. **Re-exported externally** under the Principle 15 external-audience exception: `SchedulingClass`, `PlatformError` (DLL authors depend only on `cranelisp-platform` and have no other reason to learn about `cranelisp-types`). **Window types**: none.

---

## 2. Public surface (as-designed)

`design/arch/facades/platform.md` is the authoritative public-API contract. The high-level shape:

- **Marshaling layer**: `CLType`, `CLInt`/`CLString`/`CLBool`/`CLFloat`, `CLIO<CL: CLType>`, `CLHeap`, `CLOwned<T>`. Sealed (only the four primitive wrappers + `CLIO<T>` may implement `CLType` from inside the crate; `CLHeap: CLType + Copy`).
- **C-ABI manifest**: `PlatformManifest` + `PlatformFn` + `HostCallbacks` — all `#[repr(C)]`, layout-stable contracts governed by `ABI_VERSION` per Principle 14.
- **Safe descriptor**: `OwnedPlatformFnDescriptor` — UTF-8-validated Rust mirror of `PlatformFn`, returned by `manifest_to_descriptors()`.
- **DLL author macro**: `declare_platform!` — generates the `cranelisp_platform_manifest` `extern "C"` symbol the loader looks up.
- **Constants**: `ABI_VERSION = 1`, `IO_TAG_*`, `HEAP_HEADER_SIZE`, `STRING_HEADER_BYTES`, `IO_EFFECT_RESOURCE_OFFSET`.
- **Re-exports** (per Principle 15 external-audience exception): `pub use cranelisp_types::SchedulingClass`; `pub use cranelisp_types::PlatformError` (per Decision 42, when adopted — see §3 divergence list).

Per Principle 15 the exception is justified inline in the facade: out-of-tree DLL author crates depend ONLY on `cranelisp-platform` and have no reason to depend on `cranelisp-types`. This is the only crate in the workspace that exercises the external-audience exception.

Drift detection between facade and implementation is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document. Where the implementation diverges from the facade today, §3 records it.

---

## 3. Current state (derived from `crates/cranelisp-platform/src/lib.rs`)

A single-file crate, 940 lines. Logical sections in source order:

| Lines | Section | Content |
|---|---|---|
| 1–17 | Crate header + `ABI_VERSION` | Doc, version constant, IO tag constants |
| 19–52 | Layout constants | `IO_TAG_*`, `IO_EFFECT_RESOURCE_OFFSET`, `HEAP_HEADER_SIZE` (derived from `cranelisp_types::HeapHeader::SIZE`), `STRING_HEADER_BYTES`. Re-export `cranelisp_types::SchedulingClass`. |
| 53–120 | C-ABI struct definitions | `PlatformFn`, `HostCallbacks`, `PlatformManifest` (all `#[repr(C)]`). `unsafe impl Send + Sync for PlatformFn`. |
| 122–187 | CL primitive wrappers + conversions | `#[repr(transparent)]` newtypes over `i64`: `CLInt`, `CLString`, `CLBool`, `CLFloat`. `From` conversions. |
| 189–216 | `CLType` trait | Marker trait `to_raw(self) -> i64`; impls for the four primitives. |
| 218–340 | `CLIO<CL: CLType>` | `pure()`, `effect()`, `effect_on_resource()` constructors using `get_global_alloc()`. `From` impls lifting i64/String/bool/f64 and CL primitives into `CLIO<CL>`. `call_effect_thunk` consumes the double-boxed thunk exactly once. |
| 341–418 | `CLString` payload accessor + conversions | `as_str()` reads `[len][bytes]` at `payload = base + HEAP_HEADER_SIZE`; `From<&str>` allocates via `GLOBAL_ALLOC` and writes the layout. |
| 420–533 | `CLHeap` trait + `CLOwned<T>` | Atomic RC primitives (`SeqCst` per Decision 13); `own()` (inc-on-wrap, dec-on-drop) and `into_owned_consuming()` (no-inc-on-wrap, dec-on-drop, per Decision 24). `CLString` impls `CLHeap`. |
| 535–576 | `HostContext` | `AtomicPtr<HostCallbacks>`; `init()` leaks a copy of the callbacks and stores `alloc` in `GLOBAL_ALLOC`. |
| 578–676 | `OwnedPlatformFnDescriptor` + `manifest_to_descriptors()` | Safe-Rust descriptor; UTF-8 validation of every string field; converts `SchedulingClass` from u32. |
| 678–816 | `derive_jit_name()` + `declare_platform!` macro | Three-phase macro: capture fn ptrs → derive JIT names → build leaked `&'static [PlatformFn]` array. |
| 818–940 | Tests | `into_owned_consuming` no-inc semantics; `own()` vs `into_owned_consuming` contrast; the capture-Effect pattern's RC balance. |

Public API surface that lives today: `CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<T>`, `CLOwned<T>`, `CLHeap`, `CLType`, `PlatformManifest`, `PlatformFn`, `HostCallbacks`, `OwnedPlatformFnDescriptor`, `HostContext`, `manifest_to_descriptors()`, `call_effect_thunk()`, `derive_jit_name()`, `declare_platform!`, plus the constants. Public re-export: `SchedulingClass`.

### As-built vs as-designed drift

The facade is target-stating. Recorded divergences (each is either a small refactor target tracked by FIXME or a deliberate forward-handoff):

1. **`HostCallbacks` ships only `alloc`.** The facade specifies `alloc + dec + rc_inc + invoke_closure`. Three of those (`rc_inc`, `dec`, `invoke_closure`) are tied to Decision 31 callback support — `Fn a b` parameter types are reserved per spec §10.10.1. Until callback support lands, host has no need to expose `rc_inc`/`invoke_closure` to platforms (no platform retains user closures); `dec` is a debug-helper convenience that is currently unused. **Not blocking** — the additional callbacks land when the use case lands. Tracked as forward-commitment in §8.

2. **`PlatformError` is not yet defined in this crate; `manifest_to_descriptors` returns `Result<…, String>`.** Facade pins `pub use cranelisp_types::PlatformError` per Decision 42 with `LoadFailed`/`ManifestNotFound`/`AbiVersionMismatch`/`DispatchError` variants carrying `ErrorLocation`. `int`'s `load_platform_dll` currently surfaces failures through `CranelispError::ModuleError` with stringified causes — the `(platform "name")` form's coordinates are dropped. **Tracked by FIXME 0104** (filed this pass — `/dev` work spanning `cranelisp-types` (define enum), `cranelisp-platform` (refactor `manifest_to_descriptors`), and `int` (refactor `load_platform_dll` + `Sess::format_error` arm).

3. **`HostContext::dispatch` is correctly absent.** The facade was updated this sprint (per §2.13 facade truth-telling) to formally retire `HostContext::dispatch`; direct GOT lookup via `platform_fn_ptr` on `ModuleEntry::Def` is the canonical path per Decision 26. Adding a centralised `dispatch` would re-introduce a parallel call path (Principle 7 violation). The implementation never built `dispatch`; this divergence is now resolved at the facade.

4. **`load_manifest` and `parse_type_sig` live in `int`, not in `cranelisp-platform`.** The facade names them as platform-crate entries; the implementation places `dlopen` orchestration (`load_platform_dll`) and the type-signature parser (`parse_type_sig`) in `src/platform.rs`. This is correct per BC §5 (DLL lifecycle is `int`'s; platform crate is the shared contract). The facade is mildly imprecise on placement; §3 below treats the `int`-side functions as the integration-layer's enactment of the contract this crate publishes. **Defer** — facade text could be corrected to reflect placement; minor.

5. **`PlatformFn` ABI carries more fields than the facade's reference shape.** Implementation has length pairs (`name_len`, `jit_name_len`, `type_sig_len`, `docstring_len`) and a `param_names` triplet (`*const *const u8`, `*const usize`, `usize`). The facade's reference shape uses null-terminated C strings. The implementation's length-prefixed shape is the binding ABI (changing it would bump `ABI_VERSION`); the facade is a simplified reading. **Defer** — facade text could be corrected; the implementation shape is the truth and is governed by `ABI_VERSION` per Principle 14.

6. **`OwnedPlatformFnDescriptor` carries `param_names: Vec<String>`** not in the facade's reference shape. This is owned data downstream of `param_names`/`param_name_lens` in `PlatformFn`. **Defer** — facade should mention it; trivial addition.

7. **`#[non_exhaustive]` not applied to non-`#[repr(C)]` public types.** Per Principle 14 the three `#[repr(C)]` types (`PlatformManifest`, `PlatformFn`, `HostCallbacks`) MUST NOT carry `#[non_exhaustive]` — implementation is correct. The remaining public types (`CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<T>`, `CLOwned<T>`, `OwnedPlatformFnDescriptor`) lack `#[non_exhaustive]`. The CL wrappers are `#[repr(transparent)]` — they ARE layout contracts (the JIT calling convention reads them as raw `i64`). Treating them like the `#[repr(C)]` types and exempting them from `#[non_exhaustive]` is consistent with the Principle 14 rationale (layout discipline). `OwnedPlatformFnDescriptor` is pure-Rust data, not layout-bound, and SHOULD carry `#[non_exhaustive]`. **Tracked by FIXME 0107** (filed this pass — small `/dev` cleanup adding the annotation to `OwnedPlatformFnDescriptor`; clarification request to `/arch` on the `#[repr(transparent)]` exemption rule).

8. The crate is single-file (`lib.rs`). The facade does not require multi-file structure; one file is appropriate at current scale.

`ABI_VERSION = 1` matches the facade.

---

## 4. Internal architecture overview

Single-file crate (`src/lib.rs`). Logical layers, top-down:

```
+----------------------------------------------+
|  declare_platform! macro                     |  DLL-author surface — generates the manifest extern
+----------------------------------------------+
|  CLIO<T>, CLOwned<T>, capture-RC protocol    |  Safe wrappers — platform DLL author API
|  CLInt/CLString/CLBool/CLFloat               |
|  CLType / CLHeap traits                      |
+----------------------------------------------+
|  manifest_to_descriptors,                    |  Host-side manifest parsing (called from int)
|  OwnedPlatformFnDescriptor                   |
+----------------------------------------------+
|  PlatformManifest, PlatformFn,               |  C-ABI struct contract — both sides agree
|  HostCallbacks, ABI_VERSION, IO tag consts   |
+----------------------------------------------+
|  HostContext + GLOBAL_ALLOC (per-DLL static) |  Allocator handle wired by macro at init
+----------------------------------------------+
```

The crate's two "faces" — host and DLL — share the same compiled code, but each loaded DLL gets its own copy of `GLOBAL_ALLOC` (separate compilation unit). `HostContext::init` is called inside each DLL's manifest extern by the `declare_platform!` macro; the host calls `manifest_to_descriptors` to read what each DLL exposes.

There is no internal cadence: no threads spawned, no state machines, no scheduler logic. The crate's only mutable state is the per-DLL `GLOBAL_ALLOC` `AtomicPtr` and `HostContext.callbacks` `AtomicPtr`. Both are write-once at DLL init, read-often.

---

## 5. ABI architecture

The platform calling convention is the contract that compiled cranelisp code, the IO trampoline (in runtime), and platform DLLs all agree on. Per spec §10.10.1 (current state — pre-callback): every value crosses as a single `i64`.

**Type → i64 mapping** (current ABI, version 1):

| Cranelisp type | i64 interpretation | Wrapper |
|---|---|---|
| `Int` | the integer value | `CLInt` |
| `Bool` | `0 = false`, `1 = true` | `CLBool` |
| `Float` | `f64::to_ne_bytes` reinterpreted as `i64` | `CLFloat` |
| `String` | base pointer to a heap allocation `[alloc_size, rc, len, bytes…]` | `CLString` |
| `IO a` | base pointer to a heap-allocated IO node tree (Pure/Effect/Bind/Par) | `CLIO<CL>` |
| `Fn a b` | **future** (Decision 31 forward-commitment) — heap closure pointer | not yet defined |

**IO node layout** (the structure the runtime trampoline walks). Each node starts with a `HEAP_HEADER_SIZE` (16-byte) header, then the node's tag, then per-tag fields. `CLIO::pure` and `CLIO::effect` allocate via `GLOBAL_ALLOC` at the right size and return the *base* pointer (not the payload pointer) so the trampoline reads `tag` at `base + HEAP_HEADER_SIZE`:

| Tag | Constant | Size (after header) | Fields |
|---|---|---|---|
| 0 | `IO_TAG_PURE` | 16 | `[tag, value]` |
| 1 | `IO_TAG_EFFECT` | 24 | `[tag, thunk_ptr, resource_token]` — `thunk_ptr` is a `Box<Box<dyn FnOnce() -> i64>>` ptr |
| 2 | `IO_TAG_BIND` | (set by runtime) | Internal — reserved tag, not constructed by platform DLLs |
| 3 | `IO_TAG_PAR` | (set by runtime) | Reserved for spec §10.12 automatic IO scheduling |

The double-boxed thunk on Effect nodes is a thin pointer (one `i64`) over a trait object (two `i64`s). `call_effect_thunk` reclaims via `Box::from_raw` and invokes once. The trampoline (in runtime) MUST not call `call_effect_thunk` on the same node twice — single-shot, by contract.

**Scheduling class** is a per-fn property declared in the manifest (Decision 26). It lives inside the typecheck variant `PrimitiveKind::PlatformEffect { scheduling_class }` so ill-formed states are unrepresentable. The IO trampoline / `int`'s scheduler reads `scheduling_class` to decide whether to dispatch on the IO threadpool, the CPU pool, or serialise on a resource token. Three values: `Sequential`, `Commutative`, `ResourceSerial`.

**ABI version**. `ABI_VERSION = 1` is checked at DLL load time by `int`'s `load_platform_dll`. Version mismatch is an unconditional load failure — the host refuses to call any function from an ABI-mismatched DLL. Layout drift at the C-ABI surface is governed by the version bump per Principle 14 (`#[non_exhaustive]` does NOT apply — see §6). On Decision-42 adoption the failure path will surface as `PlatformError::AbiVersionMismatch { dll, expected, found, location }` rather than a `String`.

**Cite**: Decision 26 (scheduling class on variant), Decision 42 (`PlatformError`), spec §10.10.1 (calling convention), spec §10.12 (Par scheduling — future), Principle 14.

---

## 6. FFI layout discipline (Principle 14)

Per Principle 14 — "FFI boundary types are governed by layout discipline". The three `#[repr(C)]` structs in this crate are layout-stable contracts, NOT source-stable contracts:

- `PlatformManifest`
- `PlatformFn`
- `HostCallbacks`

These do NOT carry `#[non_exhaustive]`. The absence is the signal that they are layout contracts; any field add/remove/reorder/type-change is a breaking change requiring an `ABI_VERSION` bump. The bump is checked by `int`'s `load_platform_dll` against the loaded DLL's `manifest.abi_version`; mismatch produces a clean refusal, not silent corruption.

A `#[non_exhaustive] #[repr(C)]` annotation pair would mislead maintainers — the source-level annotation says "safe to add fields", but the JIT-emitted code and platform DLL code read these structs by hard-coded byte offsets. Adding a field is *source-non-breaking* in Rust but *binary-breaking* against the JIT and the loaded DLLs.

**`#[repr(transparent)]` wrappers — rule extended.** `CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<T>`, `CLOwned<T>` are also layout contracts (the JIT calling convention reads them as raw `i64`). Implementation does not carry `#[non_exhaustive]` on them. Per `/arch`'s resolution of FIXME 0107 (Option A), Principle 14 extends to cover both `#[repr(C)]` and `#[repr(transparent)]`; the implementation is correct.

**Pure-Rust descriptor.** `OwnedPlatformFnDescriptor` is owned, post-load Rust data — not layout-bound. It SHOULD carry `#[non_exhaustive]` per the standard facade convention; FIXME 0107 captures the cleanup.

**Cite**: Principle 14, facades/platform.md §`#[non_exhaustive]` DTOs.

---

## 7. Manifest + DLL discovery

DLL discovery turns a `(platform "name")` form (parsed by frontend into `PlatformSpec`) into a loaded `Arc<DllHandle>` on `SharedState.kept_dlls`. The platform crate provides the parsing primitive; `int` owns the discovery + retention logic.

**Flow** (per `platform-dlls.md` and `src/platform.rs`):

1. **Path resolution** (`int::resolve_platform_path`). Search order: `CRANELISP_PLATFORM_PATH` env var → `{project_root}/platforms/{name}.{ext}` → `target/{debug,release}/lib<crate>.<ext>` (dev convenience) → `~/.cranelisp/platforms/`. Filename convention varies by tier (`<name>.<ext>` for tiers 1/2/4; `lib<crate>.<ext>` for cargo-output tier).
2. **`dlopen` + manifest read** (`int::load_platform_dll`). `int` opens the DLL via `libloading::Library::new(path)`, looks up the `cranelisp_platform_manifest` symbol, and calls it with a `HostCallbacks { alloc: <runtime_alloc_fn> }`. The macro-generated extern initialises the DLL's `HostContext` (which writes `GLOBAL_ALLOC`) before returning the manifest.
3. **`manifest_to_descriptors`** (in this crate): UTF-8-validates every string field, converts `SchedulingClass` from u32, returns `(name: String, version: String, Vec<OwnedPlatformFnDescriptor>)`. Today errors are stringified; Decision 42 will refactor to `Result<…, PlatformError>`.
4. **ABI version check** (in `int`). `manifest.abi_version == ABI_VERSION` — mismatch is a load failure.
5. **Manifest name validation** (in `int`). `manifest.name` MUST match the declared `PlatformSpec` name; mismatch is a compile-time error (wrong DLL on path).
6. **Type signature parsing** (in `int::parse_type_sig`). For each descriptor, the type-signature S-expression string (e.g., `(Fn [String] (IO Int))`) is parsed into the typecheck `Type` enum. Lives in `int` because the parser reaches into typecheck's type vocabulary; keeping it out of `cranelisp-platform` preserves the platform crate's freedom from the typecheck dep.
7. **Symbol-table population** (in `int`). For each descriptor, create a `ModuleEntry::Def` in synthetic module `platform.<name>` with `kind = DefKind::Primitive { primitive_kind: PlatformEffect { scheduling_class }, jit_name: Some(jit_name) }`, `platform_fn_ptr = Some(descriptor.ptr)`, `scheme = parse_type_sig(descriptor.type_sig)`, `ast = None`, `code = None`. The `PlatformDecl` on the owning module records the `dll_path` for cache restore.
8. **DLL retention** (in `int`). The loaded `libloading::Library` handle is wrapped in `Arc<DllHandle>` and inserted into `SharedState.kept_dlls: DashMap<PathBuf, Arc<DllHandle>>` per Decision 38. DLLs are **session-global** — they outlive any individual `SymbolTable` and are never unloaded mid-session (`platform-dlls.md` invariant: function pointers point into mapped DLL pages).

**Cache restore** (per `platform-registry-removal.md` §A2 — note: that doc is moving to archive; the live mechanism is summarised here): cache-load reads `.meta.json` (with schema-version envelope per Decision 34), deserialises `SymbolTable` with `platform_fn_ptr = None` (`#[serde(skip)]` field). The integration layer iterates persisted `ModuleEntry::PlatformDecl` entries, calls `load_and_register_platform` for each, and writes the freshly resolved `platform_fn_ptr` back onto each `Def`. Failure modes (DLL renamed, ABI mismatch, missing exports) invalidate the cache entry as if dependencies changed.

**Cite**: Decision 38 (`kept_dlls` location), Decision 26 (where fn ptrs and scheduling class live), Decision 42 (forward — `PlatformError` adoption replaces stringly-typed errors), `platform-dlls.md` (search path, error conditions, full loading sequence; subordinate doc to be currency-checked per §11).

---

## 8. Platform fn registration (Decision 26 + Decision 27)

Decision 27's `PlatformRegistry` deletion sequencing has **landed**. The post-G8 shape:

- Platform fn pointers live on `ModuleEntry::Def.platform_fn_ptr: Option<*const u8>` (`#[serde(skip)]`, sibling to `kind`).
- Scheduling class lives inside the variant: `PrimitiveKind::PlatformEffect { scheduling_class: SchedulingClass }`.
- The `PlatformRegistry` type is **deleted** from `int`; there is no parallel store.

The three reader sites all walk the symbol table directly:

1. **JIT symbol collection** (`int::collect_jit_setup`): walks the current module's symbols, follows Import chains to the defining `Def`, reads `platform_fn_ptr`, emits `(jit_name, fn_ptr)` to the JIT linker via `JITBuilder::symbol`.
2. **Bind-chain analysis** (`int::bind_chain_analysis::classify_expr`): resolves callee name via Import chain, pattern-matches `DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class }, .. }` to read the class.
3. **IO trampoline / scheduler**: same — reads `scheduling_class` off the destructured variant when an Effect node dispatches.

**`crates/cranelisp-platform/` is unchanged by Decision 27**. The deletion was confined to `int`. This crate continues to expose the C-ABI types, the wrappers, the descriptor type, and the macro — those were never duplicated by the registry.

**Cite**: Decision 26, Decision 27, `platform-registry-removal.md` (subordinate, archive-bound).

---

## 9. Forward-commitment: callback support (Decision 31)

The current platform calling convention (spec §10.10.1) supports `Int`, `Bool`, `String`, `Float`, `IO a`. There is no `Fn a b` row in the i64 interpretation table, so platforms today cannot receive or retain user closures. Decision 31 specifies the rules for when that row is added:

1. **Heap closure address, not raw code pointer**. The i64 passed for a fn-typed argument is the address of the heap closure struct (Decision 11 layout: `[header | code_ptr | drop_glue_ptr | captures…]`), NOT the raw JIT code pointer the closure dispatches to. Platforms never see raw JIT addresses.
2. **Host callback for invocation**. Platforms invoke retained closures via a new `HostCallbacks::invoke_closure(closure_ptr, args, n_args) -> i64` callback (added when the row lands). The callback dispatches through the closure's `code_ptr` slot, which is GOT-indirect. Result: REPL redefinition retargets future invocations transparently — even from already-retained closures.
3. **RC discipline on retention**. Platforms that store a closure beyond the dynamic extent of the receiving call MUST inc-on-store and dec-on-release via host callbacks (`rc_inc` / `rc_dec`). Retention without RC participation is an ABI contract violation.
4. **Safety invariant preserved**. Decision 31's per-batch JIT reclaim safety holds: the `Arc<Jit>` reaches refcount 0 only when no `ModuleEntry::Def.code` references it AND no live heap closure targets a GOT slot backed by it. `unsafe free_memory()` fires safely. (Per Decision 41's amendment, the per-batch model is updated to per-symbol JIT modules with a single shared `Arc<Jit>`; the reclaim invariant is preserved at finer granularity.)

**Implementation status**: zero work in this crate yet. Spec must add the row to §10.10.1 first; then this crate adds the new wrapper (`CLClosure` or similar — name TBD with `/spec`), extends `HostCallbacks` with `invoke_closure` / `rc_inc` / `rc_dec`, and extends `CLOwned<T>` semantics to closures. ABI version bumps to 2 on landing.

This section is the design landing pad; future readers should not be surprised when the row appears.

**Cite**: Decision 31 "Callback support (forward commitment)", Decision 11 (closure layout), Decision 41 (per-symbol JIT amendment), spec §10.10.1.

---

## 10. Quality attributes

Stewardship per `/design`'s charter; observed against the current source. Untouched-this-pass attributes are noted as such.

| Attribute | Assessment |
|---|---|
| **Simplicity** | Strong. Single 940-line file; no internal cadence; no shared mutable state beyond two write-once `AtomicPtr`s. The crate's purpose is "stable contract"; complexity is naturally bounded by the C-ABI surface. Principle 6 (complexity has a budget) is upheld — the crate carries only the marshaling / manifest types the spec demands. |
| **Maintainability** | Strong. `ABI_VERSION` protects layout per Principle 14. The `#[non_exhaustive]` rule for non-FFI types is partially applied (CL wrappers correctly omit it; `OwnedPlatformFnDescriptor` should add it — FIXME 0107). Boundary clean: depends only on `cranelisp-types`. Bounded blast radius for changes. |
| **Observability** | Weak. No tracing in this crate. The host-side `manifest_to_descriptors` returns `Result<…, String>` rather than a structured error; debugging a malformed DLL today produces a string with no `ErrorLocation`. Decision 42 adopting `PlatformError` (FIXME 0104) closes this. |
| **Concurrency-safety** | The crate has no threads. Concurrency invariants borne by this crate: (1) `GLOBAL_ALLOC` and `HostContext.callbacks` use `AtomicPtr` with `SeqCst`; (2) `CLHeap::inc_rc` / `dec_rc` use `AtomicI64` with `SeqCst` per Decision 13; (3) DLL handles are session-global and never unloaded — pointers into DLL code remain valid for the session, satisfying Decision 31's safety invariant for platform-emitted code paths. `unsafe impl Send + Sync for PlatformFn` is sound because the raw pointers carry process-lifetime data. |
| **Performance** | Out-of-pass — sprint did not touch perf. The marshaling is i64 passthrough where possible; only `CLString` and `CLIO<T>` allocate. `CLOwned<T>` is one inc on construct, one dec on drop (atomic SeqCst — costs a fence per RC change but is the Decision-13 contract for ABI compatibility with the future concurrent runtime). No premature optimisations. |
| **Testability** | Adequate. Inline `#[cfg(test)] mod tests` covers `into_owned_consuming` semantics, `own()` vs `into_owned_consuming` contrast, and the capture-Effect RC balance — the three behaviours most prone to regression. The ABI types (`PlatformManifest`/`PlatformFn`) are not unit-tested in isolation; their correctness is exercised by the v4_platform integration tests (in `tests/v4_pipeline.rs`). The platform crate is testable with stubs at its boundary — `manifest_to_descriptors` accepts a `&PlatformManifest` and returns owned data; nothing in the crate requires a live DLL. |

---

## 11. Decision register (platform-relevant)

Per `design/arch/CLAUDE.md`'s active-vs-legacy split: active Decisions carry forward-handoff or pre-implementation work; legacy Decisions are fully embodied in the architecture and preserved for narrative continuity. Decision 10 is environmental (rejected-alternative capture).

### Active

| # | Decision | Bearing on platform |
|---|---|---|
| 27 | G8 → G9 sequencing; `PlatformRegistry` deleted | Landed — confirms this crate's surface stable (environmental — borrow-checker sequencing rationale) |
| 31 | Per-batch JIT + custom Drop; callback support forward-commitment | Specifies the future `Fn a b` row contract — see §9 (environmental + pre-implementation forward-handoff for callback row; amended S64 per Decision 41) |
| 40 | `IoObserver` callback contract in runtime | Platform-runtime pairing: platform is downstream of runtime via `HostCallbacks`; runtime owns the `IoObserver` extension point. Platform DLLs do not register observers. (pre-implementation) |
| 41 | Per-symbol JIT cardinality; `Code` in `cranelisp-backend` | Refines Decision 31's reclaim model; platform crate unaffected (the safety invariant for `unsafe free_memory()` holds at finer granularity) (pre-implementation) |
| 42 | `PlatformError` is `cranelisp-types`-hosted with `ErrorLocation` per variant | Replaces the current `Result<…, String>` surface on `manifest_to_descriptors` and `int`'s DLL load path. `PlatformError` re-exported here per Principle 15 external-audience exception. Tracked by FIXME 0104. (pre-implementation) |

### Legacy — embodied (and environmental)

| # | Decision | Bearing on platform |
|---|---|---|
| 10 (environmental) | Base-pointer ABI | Captures rejected interior-pointer alternative; layout convention this crate honours via `HEAP_HEADER_SIZE` |
| 11 (legacy — embodied) | Embedded `drop_glue_ptr` in heap closures | Forward-commitment — Decision 31 callback row uses this layout |
| 13 (legacy — embodied) | Atomic RC `SeqCst` from Ring 1 | `CLHeap::inc_rc` / `dec_rc` use `SeqCst`, NOT `Relaxed` |
| 24 (legacy — embodied) | Uniform consuming calling convention | `CLOwned::into_owned_consuming` (no-inc-on-wrap, dec-on-drop) is the platform-side enactment |
| 26 (legacy — embodied) | `platform_fn_ptr` on `ModuleEntry::Def`; `scheduling_class` on `PrimitiveKind::PlatformEffect { … }` | Defines where the runtime data live; this crate provides the typed primitives |
| 38 (legacy — embodied) | `SharedState` formal definition; `kept_dlls: DashMap<PathBuf, Arc<DllHandle>>`; `Introspection` placement | DLL handles live in `int`; this crate is `kept_dlls`-shape-agnostic |
| 39 (legacy — embodied) | Per-defn source on `Introspection`; `ErrorLocation` carrying coordinates | Errors raised through the platform load path carry `ErrorLocation` once Decision 42 adoption lands |

**Principles cited.** Principle 6 (complexity budget — §10), Principle 7 (single source of truth — §3 divergence #3), Principle 13 (RC `SeqCst` — §10), Principle 14 (FFI layout discipline — §6), Principle 15 (external-audience exception — §1, §2).

---

## 12. Subordinate docs

The other `design/platform/` documents:

| Doc | Status | Disposition |
|---|---|---|
| `CLAUDE.md` | Current | **Keep**. Local conventions for `/platform` design work — read first when designing. |
| `platform-dlls.md` | Pre-Decision-42 references stringly-typed errors; pre-Decision-40 doesn't mention the platform-runtime pairing; pre-Principle-14 doesn't cite the layout-discipline rule. The mechanics it documents (search path, manifest format, capture-RC protocol, `cranelisp-stdio` reference platform, `cranelisp-test-capture` test platform) are all current and load-bearing. **Keep — minor refresh needed.** Refresh deferred to the same sprint that lands FIXME 0104 (PlatformError adoption) so the error-surface narrative can be updated in one pass. |
| `platform-registry-removal.md` | Work has landed (Decision 27 deletion + cache-restore addendum). Lessons folded into Decisions 26, 27, 38 and into this master + `platform-dlls.md`. **Archive-bound.** Tracked by FIXME 0106 (filed this pass — `/design`-narrow `git mv` to `design/platform/archive/platform-registry-removal.md` + one-line README, deferred to a sprint with low platform load). |
| `runtime.md` | **Mis-located.** This file is the runtime crate's design doc, not platform's. It collides namewise with `design/runtime/runtime.md` (the canonical home post-S64) and predates the per-crate-master-design baseline. **Delete.** The canonical runtime master is `design/runtime/runtime.md`; nothing in `design/platform/runtime.md` is uniquely load-bearing for the platform crate (the platform-side view of the IO trampoline contract is captured in §5 of this doc; the `call_effect_thunk` semantics in §5; the allocator wiring in §4; the platform-runtime pairing in the §10 Decision register row for Decision 40). Deletion executed this pass — git history preserves content per S64 methodology rule. |

---

## 13. Open questions / FIXMEs filed this pass

This pass files three FIXMEs (filing skill: `/design` (platform)):

| Number | Target | Summary |
|---|---|---|
| 0104 | `/dev` | Adopt `PlatformError` per Decision 42 — refactor `manifest_to_descriptors` and `int::load_platform_dll` to construct `PlatformError` rather than `String`; surface via `CranelispError::Platform`; add `Sess::format_error` arm. Spans `cranelisp-types` (define enum), `cranelisp-platform` (refactor), `int` (refactor + format arm). |
| 0107 | `/dev` | Add `#[non_exhaustive]` to `OwnedPlatformFnDescriptor` (`/arch` resolved Option A — extending Principle 14 to cover both `#[repr(C)]` and `#[repr(transparent)]`; `OwnedPlatformFnDescriptor` is the only public type with no FFI repr annotation and SHOULD carry `#[non_exhaustive]`). |
| 0106 | `/design` (self) | Archive `platform-registry-removal.md` to `design/platform/archive/` after one final cross-check against canonical citations (this master + Decisions 26/27/38). 30-min housekeeping pass. |

**Already-tracked, no new FIXME this pass:**

- FIXME 0101 (`/sprint`) covers the platform audit pass (sequenced after Decision 40 / FIXME 0103 lands).
- FIXME 0103 (`/dev`, runtime + int) covers the `IoObserver` relocation per Decision 40 — affects platform indirectly (the platform-runtime pairing in BC §4) but no platform-crate work.
- The `HostCallbacks` expansion (`rc_inc`, `rc_dec`, `invoke_closure`) is forward-commitment per Decision 31 §9 and is intentionally NOT a FIXME today — it lands when spec §10.10.1 adds the `Fn a b` row.
- The `load_manifest` / `parse_type_sig` placement mismatch (facade names them in platform; implementation places them in `int`) is a minor facade text correction — not a `/dev` change. Deferred without FIXME — `/arch` may opportunistically correct facade text to reflect the BC §5 placement.

---

## Cross-references

- `design/arch/facades/platform.md` — public-API contract (authoritative)
- `design/arch/facades/runtime.md` — runtime's facade (consumes platform's `HostContext` for the IO trampoline; `IoObserver` per Decision 40)
- `design/arch/facades/types.md` — `SchedulingClass`, `PlatformSpec`, `ErrorLocation`, `PlatformError` (Decision 42)
- `design/arch/bounded-contexts.md` §5 — Platform bounded context
- `design/arch/principles.md` — architectural principles index (Principles 6, 7, 13, 14, 15 cited above)
- `design/arch/CLAUDE.md` — Decisions index (11, 13, 24, 26, 27, 31, 38, 39, 40, 41, 42 cited above)
- `design/platform/platform-dlls.md` — DLL loading mechanics (subordinate; refresh deferred to FIXME 0104 sprint)
- `design/platform/archive/platform-registry-removal.md` — G8 deletion (subordinate; pending move per FIXME 0106)
- `crates/cranelisp-platform/src/lib.rs` — current implementation (single file, 940 lines)
- `src/platform.rs` — `int`'s platform load + path resolution + type signature parser (the integration-side enactment of this crate's contract)
