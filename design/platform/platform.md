# Platform — Master Design

`crates/cranelisp-platform/` — the shared interface contract between the cranelisp host binary and platform DLLs. Both sides depend on this crate; that is its purpose. It owns the C-ABI types, the safe wrappers presenting those types in Rust, the layout constants both sides must agree on, the macro DLLs use to publish their manifests, and the marshalling helpers that keep RC discipline correct across the DLL boundary.

This is the master design doc per `/design`'s charter. Subordinate topic docs in `design/platform/` are listed in §11 and cited by section.

> **Note (audited 2026-06-14).** The platform audit pass landed — `audits/platform-2026-06-14.md` is the structural snapshot after the S71 ADT-marshaling redesign, the S76 three-exports rework, and the S81 fault-guarded dispatch funnel (ABI v5). §3 below is refreshed against that audit's File Metrics + public-surface census + the BC §5 nine-invariant conformance table (FIXME 0372, S84 `/design`). FIXME 0101 (the audit pass) is discharged on the platform half. Per-item public-API truth is the crate-root `//!` + per-item `///` rustdoc; this doc carries the cross-surface shape, not a re-derived surface list.

---

## 1. Bounded-context recap

Per `design/arch/bounded-contexts.md` §5 — platform is the *shared interface contract crate*. It exposes the C-ABI types, the wrappers, the layout constants, and the manifest macro. It owns **no session-coordinated state and no cadence**; the only state it holds is three per-DLL write-once globals (`GLOBAL_ALLOC`, `GLOBAL_ALLOC_WITH_TAG` — `AtomicPtr` allocator slots; `GLOBAL_SCHEMA` — a `OnceLock<Schema>`), each set once at DLL load (`HostContext::init` / `set_global_schema`) and bounded by BC §5 invariant 6 (no DLL unloading mid-session). (LOW-1, audit 2026-06-14 — corrects the literal "owns no runtime state"; a BC §5 phrasing refresh is filed to `/arch`, see §13.)

**Owns**:
- ABI value wrappers — `CLType` trait, `CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<T>`, `CLOwned<T>`, `CLHeap` trait
- C-ABI manifest types — `PlatformManifest`, `PlatformFn`, `HostCallbacks` (all `#[repr(C)]`)
- Manifest parsing — `manifest_to_descriptors()` → `OwnedPlatformFnDescriptor`
- Effect-thunk consumption primitive — `call_effect_thunk` (single-shot, called from runtime)
- Constants — `ABI_VERSION` (= **7**), `IO_TAG_PURE`/`IO_TAG_EFFECT`/`IO_TAG_BIND`/`IO_TAG_PAR`, `HEAP_HEADER_SIZE`, `IO_EFFECT_RESOURCE_OFFSET` (16), `IO_EFFECT_FN_NAME_OFFSET` (24, ABI v4), `IO_EFFECT_CAPACITY_OFFSET` (32, S95 slice-3 carrier), `STRING_HEADER_BYTES`
- Resource/capacity effect constructors — `CLIO::effect_on_resource(token, f)` and the additive sibling `CLIO::effect_on_resource_with_capacity(token, capacity, f)` (S95 slice-3 carrier; `effect_on_resource(token, f) = …_with_capacity(token, 1, f)`)
- DLL author macro — `declare_platform!` (the single unified emitter in `declare.rs`; one platform mixes blocking effects via the per-fn `scheduling:` key and poll-shape async leaves via `descriptor:` in ONE manifest). The former `concurrency`-gated `declare_concurrent_platform!` was **deleted** in the single-ABI cutover — its poll-shape arm folded into `declare_platform!`.
- Host-reactor C-ABI contract types (`concurrency.rs`, now core/ungated) — `HostCtx`, `Waker`, `WakerVTable`, `PollFn` (+ `cranelisp_types::{ConcurrencyDescriptor, Poll}` re-exports). The former dual-channel `ConcurrentPlatformFn` / `ConcurrentPlatformManifest` were **deleted** in the single-ABI cutover — absorbed into the unified `PlatformFn` / `PlatformManifest`.
- `concurrency`-gated `poll_support` ergonomics module (S96) — typed env accessor + fd/timer reactor scaffold + `PollState` phase scaffold (`design/platform/poll-support.md`)
- Per-DLL write-once globals — `HostContext`, the two allocator slots (`GLOBAL_ALLOC`, `GLOBAL_ALLOC_WITH_TAG`), and the schema `OnceLock` (`GLOBAL_SCHEMA` in `adt.rs`)
- ADT marshaling — `CLAdt<T>` heap-ADT wrapper, `CLAdtType` marker trait, `EffectOutcome` `#[repr(C)]` fault-outcome carrier
- Schema parser — `Schema`/`TypeShape`/`Ctor`/`Field` + the tiny S-expr lexer/parser (`schema.rs`), reading the backend-generated `/platform-schema` artifact for name→offset field lookup
- Layout-hash extraction — `extract_layout_hash()` (const-fn over the embedded artifact header)

**Does not own**:
- DLL lifecycle storage — `SharedState.kept_dlls: DashMap<PathBuf, Arc<DllHandle>>` lives in `int`. Path search, `dlopen`, ABI version validation, and lifecycle orchestration also live in `int` (`src/platform.rs::load_platform_dll`, `resolve_platform_path`).
- IO trampoline — owned by `cranelisp-intrinsics` (the backend-emitted runtime library; the former `cranelisp-runtime` was split at D43). Platform exposes `call_effect_thunk` and the IO node tag layout; the runtime library reduces the tree.
- `IoObserver` callback contract — owned by `cranelisp-intrinsics` per Decision 40 (the registration host moved with the D43 split). Platform DLLs do not register observers; the runtime library does.
- Scheduling decisions — `int`'s scheduler reads `scheduling_class` off `PrimitiveKind::PlatformEffect` to choose threadpool/serialisation.
- Platform fn dispatch at runtime — **GOT-indirect** (`got_slot = manifest index`; the host's `GotTable` wraps the dlsym'd DLL GOT in place — BC §5 invariant 1). The S71-era `platform_fn_ptr`-on-`ModuleEntry::Def` field and `JITBuilder::symbol`/`derive_jit_name` name-dispatch are **retired** (S76–S80 three-exports landing).
- Type signature parsing — `parse_type_sig` lives in `int` (`src/platform.rs`), invoked at platform-load time after `manifest_to_descriptors` returns the raw string.
- Per-DLL platform implementations — separate downstream crates (e.g., `platforms/stdio/`).
- Spec for IO semantics — `/spec` (`spec/10-io.md`).

**Crosses the boundary outward**: C-ABI types, wrappers, constants, and the macro — to both host and DLL consumers. **Inward**: `SchedulingClass`, `HeapHeader` from `cranelisp-types`. **Re-exported externally** under the Principle 15 external-audience exception: `SchedulingClass`, `PlatformError` (DLL authors depend only on `cranelisp-platform` and have no other reason to learn about `cranelisp-types`). **Window types**: none.

---

## 2. Public surface (as-designed)

`crates/cranelisp-platform/src/lib.rs` `//!` + per-item `///` rustdoc plus `design/arch/bounded-contexts.md` §5 carry the authoritative public-API narrative (facade retired S71 Wave 4 — 3rd data point of the facade-retirement pattern). The high-level shape:

- **Marshaling layer**: `CLType`, `CLInt`/`CLString`/`CLBool`/`CLFloat`, `CLIO<CL: CLType>`, `CLHeap`, `CLOwned<T>`. Sealed (only the four primitive wrappers + `CLIO<T>` may implement `CLType` from inside the crate; `CLHeap: CLType + Copy`).
- **ADT marshaling layer** (S71+, `adt.rs`): `CLAdt<T>` heap-ADT wrapper, `CLAdtType` marker trait, `CLTypeWitness`/`ExpectedFieldType`; `read_field`/`own_field`/`read_tag`/`construct` over the `GLOBAL_SCHEMA` name→offset resolution.
- **C-ABI manifest**: `PlatformManifest` + `PlatformFn` + `HostCallbacks` + `EffectOutcome` — all `#[repr(C)]`, layout-stable contracts governed by `ABI_VERSION` per Principle 14. `EffectOutcome` is the fault-outcome carrier the DLL-local `catch_unwind` ferries back (ABI v4→v5, §9a).
- **Safe descriptor**: `OwnedPlatformFnDescriptor` — UTF-8-validated Rust mirror of `PlatformFn`, returned by `manifest_to_descriptors()`.
- **DLL author macro**: `declare_platform!` (+ the internal `__declare_platform_body!`) — the **three-exports** emitter: the GOT (`__cranelisp_got_platform_<name>`), the `cranelisp_platform_manifest` extern, and (with the `schema:` arm) the `__cranelisp_layout_hash_<name>` data symbol. `extract_layout_hash()` is the const-fn it uses to pull the hash from the embedded artifact.
- **Schema parser** (`schema.rs`): `Schema`/`TypeShape`/`Ctor`/`Field`/`FieldType` + a tiny S-expr lexer/parser, total and frontend-independent (Principle 3), reading the backend-generated `/platform-schema` artifact for `read_field` name→index resolution.
- **Constants**: `ABI_VERSION = 7`, `IO_TAG_*` (incl. the reserved `IO_TAG_EFFECT_POLL`, gated), `HEAP_HEADER_SIZE`, `STRING_HEADER_BYTES`, `IO_EFFECT_RESOURCE_OFFSET = 16`, `IO_EFFECT_FN_NAME_OFFSET = 24`, `IO_EFFECT_CAPACITY_OFFSET = 32`.
- **Re-exports** (per Principle 15 external-audience exception): `pub use cranelisp_types::SchedulingClass`; `pub use cranelisp_types::PlatformError` (per Decision 42, when adopted — see §3 divergence list).

Per Principle 15 the exception is justified inline in the facade: out-of-tree DLL author crates depend ONLY on `cranelisp-platform` and have no reason to depend on `cranelisp-types`. This is the only crate in the workspace that exercises the external-audience exception.

Drift detection between facade and implementation is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document. Where the implementation diverges from the facade today, §3 records it.

---

## 3. Current state (as-built — audit 2026-06-14; ABI/file refresh S96 FIXME 0461)

> **S96 refresh (FIXME 0461 drain).** The audit headline below was written at
> ABI v5 / three files. As-built today the stamp is **ABI v7** and the crate is
> **five files** — the macro pair split out to `declare.rs` (S84 MED-4 extract),
> and the v7 host-reactor C-ABI contract types landed in `concurrency.rs`
> (`#[cfg(feature = "concurrency")]`, off the default edge). Two bumps since the
> audit: **v6** (S86 — namespaced manifest export `cranelisp_platform_manifest_<name>`,
> DEF-5) and **v7** (S93 — the effect-concurrency ABI-v4 cascade, `concurrency`-gated
> contracts). The S95 slice-3 **capacity carrier** also landed: the
> `CLIO::effect_on_resource_with_capacity(token, capacity, f)` constructor + the
> `IO_EFFECT_CAPACITY_OFFSET = 32` const (the `IO_TAG_EFFECT` payload widens
> 32 → 40, **append-only**). See the refreshed "ABI version history" + "Capacity
> carrier" below; the canonical surfaces remain the source rustdoc +
> `io-trampoline.md` §13 / `effect-concurrency.md` §8.1 / `platform-interface.md`
> §6.8.

The crate is **five files, ABI v7**, dispatching **GOT-indirect** with **ADT marshaling**. It has cleanly absorbed five major reworks since the S71-era reading this section used to describe: S71 ADT marshaling, S76 three-exports, S81 fault-guarded dispatch funnel, S86 manifest-export namespacing (v6), S93 effect-concurrency ABI-v7 cascade (gated). The audit's verdict (at v5): it **conforms to all nine BC §5 invariants and the three-exports model**, with **no HIGH findings**.

### File metrics (from `audits/platform-2026-06-14.md`)

| File | Source | Tests | Responsibility |
|---|---:|---:|---|
| `src/lib.rs` | ~1,779 | ~762 (24) | Crate facade + rustdoc (rustdoc IS the facade — Principle 15 exception); CL\* wrapper family (`CLInt`/`Bool`/`Float`/`String`/`IO`/`Owned`); the `#[repr(C)]` contract types (`PlatformFn`, `HostCallbacks`, `PlatformManifest`, `EffectOutcome`); layout constants; `HostContext`; `manifest_to_descriptors`; `extract_layout_hash`; `declare_platform!` + `__declare_platform_body!`; the per-DLL allocator statics |
| `src/schema.rs` | ~660 | ~115 (8) | `/platform-schema` artifact parser: `Schema`/`TypeShape`/`Ctor`/`Field`/`FieldType`/`ParseLoc`/`SchemaParseError`; tiny S-expr lexer/parser; field-offset + field-type lookups |
| `src/adt.rs` | ~370 | ~130 (6) | `CLAdt<T>` heap-ADT wrapper; `CLAdtType` marker trait; `CLTypeWitness`/`ExpectedFieldType`; `GLOBAL_SCHEMA` `OnceLock` + `set_global_schema`; `read_field`/`own_field`/`read_tag`/`construct`; name→offset resolution |

Integration tests live under `tests/` (866 lines, 6 files: `worked_examples`, `macro_expansion`, `baseline`, `cl_adt_sums`, `cl_adt_products`, `macro_full_arm_compile`) and exercise the macro + ADT marshaling end-to-end.

**Public surface census** (audit): 19 `pub struct`, 5 `pub trait`, 3 `pub enum`, 17 free `pub fn`, 9 constants, 1 macro, 2 re-exports (`SchedulingClass`, `PlatformError`). `unsafe`: 3 `unsafe fn` (`call_effect_thunk`, `HostContext::init`, `manifest_to_descriptors`), 4 `unsafe impl`. Zero inline `FIXME`/`TODO`/`deprecated` work-markers. The per-item public-API truth is the crate-root `//!` + per-item `///` rustdoc + `audits/platform-2026-06-14.md`'s census — this doc does not re-derive the item list.

### Dispatch model — GOT-indirect (the headline change from the old §3)

Dispatch is **GOT-indirect by `got_slot = manifest index`**, NOT the S71-era `JITBuilder::symbol`-by-`jit_name` mechanism. The `declare_platform!` macro emits the **three exports** (platform-interface.md §1):

1. **GOT** — `__cranelisp_got_platform_<name>`: a const-init pointer table, slot *i* = fn *i*, populated by the linker (relocations: dynamic loader for dylib, static linker for `--link`) — no runtime population.
2. **Manifest** — `cranelisp_platform_manifest`: the `extern "C"` entry the loader looks up; the host builds its `SymbolTable` from manifest facts (name + FQ `type_sig`→scheme + `got_slot` = manifest index + `scheduling_class` + metadata).
3. **Schema + layout-hash** (with the `schema:` arm) — `__cranelisp_layout_hash_<name>`: a `&'static str` data symbol the host regenerates-and-compares (REPL warns, `--run`/`--link` refuse).

The host's `GotTable` **wraps the dlsym'd DLL GOT in place — no copy** (BC §5 invariant 1). `derive_jit_name`, `platform_fn_ptr`-on-`ModuleEntry::Def`, the schema *declaration* DSL (`LazyLock<Schema>`-as-DSL, marker auto-emission, `validate_schema`, `schema_literal`), and `inject_primitives_import_for_platform` are all **retired in source** — only the schema *parser* survives, repointed at the generated-artifact grammar.

### Fault-guarded dispatch (ABI v4→v5)

The DLL-local fault catch (FIXME 0327 Option A, S81) is monomorphised into the DLL at the `CLIO::effect*` call site: a panic in a platform closure is caught by the DLL's own `catch_unwind` and ferried back as a `#[repr(C)] EffectOutcome` value — the only sound design across the cdylib-static-runtime boundary. `call_effect_thunk` returns `EffectOutcome`; the `IO_TAG_EFFECT` node is widened to 32 bytes with a reserved fn-name field. Design rationale: §9a; `EffectOutcome`'s rustdoc. This is what drove `ABI_VERSION` from 4 to 5.

### ABI version history

`ABI_VERSION = 7` (was `1` in the S71-era reading this section replaced). The bump trail (canonical in the `ABI_VERSION` rustdoc): **v1** primitive marshaling → **v2** S71 ADT marshaling (`alloc_with_tag`, schema DSL) → **v3** S76 three-exports (`validate_schema` removed, layout-hash gate) → **v4** S81 fn-name node widen (`IO_EFFECT_FN_NAME_OFFSET = 24`; the `IO_TAG_EFFECT` node 24 → 32) → **v5** S81 EffectOutcome / DLL-local fault-catch (`call_effect_thunk` returns `EffectOutcome`) → **v6** S86 namespaced manifest export (`cranelisp_platform_manifest_<name>`, DEF-5; resolves the two-platforms-one-binary symbol collision) → **v7** S93 effect-concurrency ABI-v4 cascade (the poll-shape async-leaf boundary: `ConcurrentPlatformFn`/`PollFn` + `HostCtx`/`Waker` host-reactor C-ABI + `ConcurrencyDescriptor` subsuming `scheduling_class`; **landed-and-dormant behind the off-by-default `concurrency` feature**, so the default `public-api.txt` edge stays byte-identical-when-off — the `_neg` frozen-edge guard enforces this). `int`'s `load_platform_dll` refuses any DLL whose `manifest.abi_version != ABI_VERSION` (Principle 14; on mismatch → `PlatformError::AbiVersionMismatch`). The v7 stamp is bumped now (in-workspace host + DLLs rebuild together) even though the macro still emitted the v6 `PlatformFn` shape until a platform opted into the poll-shape arm — v7 was **not frozen** (no out-of-tree cdylib had shipped against it), which is why the S94 R1 `drop_state` reserve + the S95 capacity slots could be appended in place with no further bump. *(Historical: the separate `declare_concurrent_platform!` macro named just above, and the v7 `ConcurrentPlatformFn`/`ConcurrentPlatformManifest` types, were superseded by the later single-ABI cutover, which deleted them and folded the poll-shape arm into the one `declare_platform!` macro. This paragraph records the v7-era ABI bump trail, not the current stamp.)*

### Capacity carrier (S95 slice 3 — `effect_on_resource_with_capacity`)

The `IO_TAG_EFFECT` node carries a fourth concurrency coordinate beyond the
`resource_token` (offset 16) and the fn-name handle (offset 24): a **capacity**
at `IO_EFFECT_CAPACITY_OFFSET = 32`. The additive sibling constructor
`CLIO::effect_on_resource_with_capacity(token, capacity, f)` appends it (the node
widens 32 → 40 bytes, **append-only — no existing offset moves**), and
`effect_on_resource(token, f)` lowers to `…_with_capacity(token, 1, f)` (today's
serial-within-token). This is the platform-supplied `(token, capacity)` carrier
the trampoline reads to run a `Semaphore(capacity)` per token (arch §8.1; reactor.md
§2.8 owns the pool). Capacity is per-**resource** (per-token), platform-supplied
**dynamically at the effect site** — NOT a static `DefKind` field. S95 proved it
on the **blocking carrier** (the synthetic `platforms/pool-demo` test leaf —
`pool-read`/`pool-write`/`pool-log`, all declaring `(token, capacity)` via the new
constructor — a blocking sibling of the `test-capture` test platform); the
**poll-shape** carrier (`IO_TAG_EFFECT_POLL` reserving the same `(token, capacity)`
slots) + live capacity-N supply + acquire-around-poll is **S96 Chunk A** (the web
reactor connection pool — `poll-support.md`).

### As-built vs as-designed — BC §5 conformance (audit)

The audit's nine-invariant table (`audits/platform-2026-06-14.md` §"As-designed vs as-built") is the authoritative conformance record; the crate satisfies all nine. Summary of the load-bearing ones:

- **Inv. 1** (GOT dispatch): implemented in the macro — const-init + populate, manifest order = slot order; host-side wrap is int's.
- **Inv. 2** (stable C ABI, bump on layout change): `ABI_VERSION = 5`; refusal is int's; tested.
- **Inv. 3** (heap closures via GOT, not raw code pointers): **future work, correctly absent** — `HostCallbacks` carries only `alloc` + `alloc_with_tag`; the rustdoc documents the future `rc_inc`/`rc_dec`/`invoke_closure` widening (§9).
- **Inv. 4** (marshaling tags shared with intrinsics; one i64 per CLType): implemented; constants derived from `cranelisp_types::HeapHeader::SIZE`, no duplication.
- **Inv. 9** (fault-guarded dispatch funnel; DLL-local catch; `EffectOutcome` C-ABI value): implemented on the platform side (the funnel's int/backend half is the open §9a work, 0289-item-5).

**The only divergences are documentation staleness (the §3 this pass refreshed) and one residual field** (`PlatformFn.ptr` still carries the fn pointer redundantly with the GOT). Neither is a contract violation. `PlatformError` IS defined (in `cranelisp-types`, Decision 42) and re-exported; the S71-era "not yet defined / returns `Result<…, String>`" divergence list above this refresh replaced is itself stale and removed.

### Migration residue — the R1 `null_alloc_with_tag` gate (`/dev` follow-up)

`null_alloc_with_tag`'s panic message + rustdoc + the `HostContext::init` comment + the `t25_null_alloc_with_tag_panic_message_contract` test still describe `alloc_with_tag` as "not yet wired by the host … host-wiring sprint scope … FIXME 0229 … will be removed", **but FIXME 0229 is resolved and the host wired `alloc_with_tag` in S76** (the BC §5 "ABI v3" rustdoc block in the same file correctly says so — the crate contradicts itself). The gate is **not dead code**: it is the correct permanent fallback when no host has called `HostContext::init` (e.g. a `cranelisp-platform` unit test exercising a construction path). The text is stale, not the gate. This is a **`/dev` code change** (MED-2 — out of `/design` scope), tracked in §13.

---

## 4. Internal architecture overview

Three-file crate: `lib.rs` (the facade + CL\* wrappers + `#[repr(C)]` contract types + constants + `HostContext` + macro), `schema.rs` (the `/platform-schema` artifact parser), `adt.rs` (`CLAdt<T>` + `GLOBAL_SCHEMA`). Logical layers, top-down:

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

**Type → i64 mapping** (current ABI, version 7):

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
| 1 | `IO_TAG_EFFECT` | **40** (ABI v7; S95 capacity widen) | `[tag, thunk_ptr, resource_token, fn_name, capacity]` — `thunk_ptr` is a `Box<Box<dyn FnOnce() -> i64>>` ptr; `resource_token` @16, `fn_name` @24 (the dispatch funnel coordinate, §9a), `capacity` @32 (`IO_EFFECT_CAPACITY_OFFSET`, the S95 slice-3 carrier — `effect_on_resource(token, f)` writes capacity 1). Append-only — no existing offset moved. |
| 2 | `IO_TAG_BIND` | (set by runtime) | Internal — reserved tag, not constructed by platform DLLs |
| 3 | `IO_TAG_PAR` | (set by runtime) | spec §10.12 automatic IO scheduling |
| 4 | `IO_TAG_EFFECT_POLL` | 16 payload (`concurrency`-gated) | `[tag, state_closure]` — the poll-shape async-leaf node; field-0 is a host-built state-closure (`[header | code_ptr=poll-fn | drop_glue | env]`); the `(token, capacity)` reserve the same slots. Built by the **backend** (io-trampoline §12), not the DLL. |

The double-boxed thunk on Effect nodes is a thin pointer (one `i64`) over a trait object (two `i64`s). `call_effect_thunk` reclaims via `Box::from_raw`, invokes once **under the DLL-local `catch_unwind`**, and returns a `#[repr(C)] EffectOutcome` (ABI v4→v5 — the fault-outcome carrier; §9a). The trampoline (in intrinsics) MUST not call `call_effect_thunk` on the same node twice — single-shot, by contract.

**Scheduling class** is a per-fn property declared in the manifest (Decision 26). It lives inside the typecheck variant `PrimitiveKind::PlatformEffect { scheduling_class }` so ill-formed states are unrepresentable. The IO trampoline / `int`'s scheduler reads `scheduling_class` to decide whether to dispatch on the IO threadpool, the CPU pool, or serialise on a resource token. Three values: `Sequential`, `Commutative`, `ResourceSerial`.

**ABI version**. `ABI_VERSION = 5` is checked at DLL load time by `int`'s `load_platform_dll`. Version mismatch is an unconditional load failure — the host refuses to call any function from an ABI-mismatched DLL. Layout drift at the C-ABI surface is governed by the version bump per Principle 14 (`#[non_exhaustive]` does NOT apply — see §6). The failure path surfaces as `PlatformError::AbiVersionMismatch { … }` (Decision 42 — adopted; `PlatformError` lives in `cranelisp-types` and is re-exported here), not a bare `String`.

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

**Cite**: Principle 14; `crates/cranelisp-platform/src/lib.rs` crate-root `//!` (`#[non_exhaustive]` discipline section) and per-item rustdoc on `CLOwned<T>` / `OwnedPlatformFnDescriptor` (facade retired S71 Wave 4).

---

## 7. Manifest + DLL discovery

DLL discovery turns a `(platform "name")` form (parsed by frontend into `PlatformSpec`) into a loaded `Arc<DllHandle>` on `SharedState.kept_dlls`. The platform crate provides the parsing primitive; `int` owns the discovery + retention logic.

**Flow** (per `platform-dlls.md` and `src/platform.rs`):

1. **Path resolution** (`int::resolve_platform_path`). Search order: `CRANELISP_PLATFORM_PATH` env var → `{project_root}/platforms/{name}.{ext}` → `target/{debug,release}/lib<crate>.<ext>` (dev convenience) → `~/.cranelisp/platforms/`. Filename convention varies by tier (`<name>.<ext>` for tiers 1/2/4; `lib<crate>.<ext>` for cargo-output tier).
2. **`dlopen` + manifest read** (`int::load_platform_dll`). `int` opens the DLL via `libloading::Library::new(path)`, looks up the `cranelisp_platform_manifest` symbol, and calls it with a `HostCallbacks { alloc: <runtime_alloc_fn> }`. The macro-generated extern initialises the DLL's `HostContext` (which writes `GLOBAL_ALLOC`) before returning the manifest.
3. **`manifest_to_descriptors`** (in this crate, `unsafe fn`): UTF-8-validates every string field, converts `SchedulingClass` from u32, returns `(name, version, Vec<OwnedPlatformFnDescriptor>)`. Failures surface as `PlatformError::LoadFailed` (Decision 42 — adopted).
4. **ABI version check** (in `int`). `manifest.abi_version == ABI_VERSION` — mismatch is a load failure.
5. **Manifest name validation** (in `int`). `manifest.name` MUST match the declared `PlatformSpec` name; mismatch is a compile-time error (wrong DLL on path).
6. **Type signature parsing** (in `int::parse_type_sig`). For each descriptor, the type-signature S-expression string (e.g., `(Fn [String] (IO Int))`) is parsed into the typecheck `Type` enum. Lives in `int` because the parser reaches into typecheck's type vocabulary; keeping it out of `cranelisp-platform` preserves the platform crate's freedom from the typecheck dep.
7. **Symbol-table population** (in `int`). For each descriptor, create a `ModuleEntry::Def` in synthetic module `platform.<name>` with `kind = DefKind::PlatformEffect { scheduling_class, got_slot }` (the callable `DefKind` carrying its own `got_slot` per Principle 20 — the slot index moved off the flat field onto the callable variant, S83), `scheme = parse_type_sig(descriptor.type_sig)`. Dispatch is **GOT-indirect**: `got_slot = manifest index`, and the host's `GotTable` wraps the dlsym'd `__cranelisp_got_platform_<name>` in place — **no `platform_fn_ptr`, no `jit_name`, no `JITBuilder::symbol`** (all retired S76–S80). The `PlatformDecl` on the owning module records the `dll_path` for cache restore.
8. **DLL retention** (in `int`). The loaded `libloading::Library` handle is wrapped in `Arc<DllHandle>` and inserted into `SharedState.kept_dlls: DashMap<PathBuf, Arc<DllHandle>>` per Decision 38. DLLs are **session-global** — they outlive any individual `SymbolTable` and are never unloaded mid-session (`platform-dlls.md` invariant: the GOT and function pointers point into mapped DLL pages).

**Cache restore**: cache-load reads `.meta.json` (schema-version envelope per Decision 34) and deserialises the `SymbolTable`. The integration layer iterates persisted `ModuleEntry::PlatformDecl` entries and calls `load_and_register_platform` for each, re-`dlopen`ing the DLL and re-wrapping its GOT (the GOT is process memory, never serialised). The **layout-hash gate** (`__cranelisp_layout_hash_<name>` regenerated from live tables and compared) is the deployment-drift guard: `--run`/`--link` refuse a mismatch, REPL warns-and-loads. Failure modes (DLL renamed, ABI mismatch, missing exports, hash mismatch) invalidate the cache entry as if dependencies changed.

**Cite**: Decision 38 (`kept_dlls` location), Decision 42 (`PlatformError` — adopted), Principle 20 (`got_slot` on the callable `DefKind`), `platform-interface.md` §1 (three exports / GOT-indirect), `platform-dlls.md` (search path, error conditions; subordinate doc to be currency-checked per §11).

---

## 8. Platform fn dispatch — GOT-indirect (S76–S80 three-exports landing)

Dispatch is **GOT-indirect by `got_slot = manifest index`** (BC §5 invariant 1; platform-interface.md §1). The S71-era model this section used to describe — `platform_fn_ptr` on `ModuleEntry::Def`, `jit_name` derivation, and JIT-symbol registration via `JITBuilder::symbol` — is **fully retired**. The post-landing shape:

- **No per-entry fn pointer.** The callable address lives in the GOT, indexed by `got_slot` (which lives on the callable `DefKind::PlatformEffect { scheduling_class, got_slot }` variant per Principle 20 — S83). There is no `platform_fn_ptr` field and no `PlatformRegistry` (the latter deleted G8, Decision 27).
- **GOT wrap, no copy.** The host's `GotTable` wraps the dlsym'd `__cranelisp_got_platform_<name>` in place (BC §5 invariant 3) — the linker (dynamic loader for dylib, static linker for `--link`) has already fixed up the slots via relocations; there is no runtime population on the host side.
- **Scheduling class** lives inside the variant (`scheduling_class: SchedulingClass`); the IO trampoline / `int`'s scheduler reads it off the destructured variant when an Effect node dispatches.

The reader sites (JIT call-emission, bind-chain analysis, the trampoline scheduler) all resolve through the symbol table + GOT — there is no parallel store and no name-based linker dispatch.

**`crates/cranelisp-platform/` emits the GOT** (via `declare_platform!`) but holds no dispatch state itself — the host owns the `GotTable` wrap. This crate continues to expose the C-ABI types, the wrappers, the descriptor type, the schema parser, and the macro.

**Cite**: BC §5 invariants 1 + 3, Principle 20 (`got_slot` on the callable variant), Decision 27 (`PlatformRegistry` deletion), platform-interface.md §1 (three exports), `audits/platform-2026-06-14.md` (`PlatformFn.ptr` residual-field note).

---

## 9. Forward-commitment: callback support (Decision 31)

The current platform calling convention (spec §10.10.1) supports `Int`, `Bool`, `String`, `Float`, `IO a`. There is no `Fn a b` row in the i64 interpretation table, so platforms today cannot receive or retain user closures. Decision 31 specifies the rules for when that row is added:

1. **Heap closure address, not raw code pointer**. The i64 passed for a fn-typed argument is the address of the heap closure struct (Decision 11 layout: `[header | code_ptr | drop_glue_ptr | captures…]`), NOT the raw JIT code pointer the closure dispatches to. Platforms never see raw JIT addresses.
2. **Host callback for invocation**. Platforms invoke retained closures via a new `HostCallbacks::invoke_closure(closure_ptr, args, n_args) -> i64` callback (added when the row lands). The callback dispatches through the closure's `code_ptr` slot, which is GOT-indirect. Result: REPL redefinition retargets future invocations transparently — even from already-retained closures.
3. **RC discipline on retention**. Platforms that store a closure beyond the dynamic extent of the receiving call MUST inc-on-store and dec-on-release via host callbacks (`rc_inc` / `rc_dec`). Retention without RC participation is an ABI contract violation.
4. **Safety invariant preserved**. Decision 31's per-batch JIT reclaim safety holds: the `Arc<Jit>` reaches refcount 0 only when no `ModuleEntry::Def.code` references it AND no live heap closure targets a GOT slot backed by it. `unsafe free_memory()` fires safely. (Per Decision 41's amendment, the per-batch model is updated to per-symbol JIT modules with a single shared `Arc<Jit>`; the reclaim invariant is preserved at finer granularity.)

**Implementation status**: zero work in this crate yet. Spec must add the row to §10.10.1 first; then this crate adds the new wrapper (`CLClosure` or similar — name TBD with `/spec`), extends `HostCallbacks` with `invoke_closure` / `rc_inc` / `rc_dec`, and extends `CLOwned<T>` semantics to closures. ABI version bumps from its current value (5) on landing.

This section is the design landing pad; future readers should not be surprised when the row appears.

**Cite**: Decision 31 "Callback support (forward commitment)", Decision 11 (closure layout), Decision 41 (per-symbol JIT amendment), spec §10.10.1.

---

## 9a. Fault-guarded FFI dispatch — the dispatch funnel (S81 PHASE 3 design — 0289-item-5)

This section designs the substantive new platform feature S81 carries: the
**fault-guarded FFI-dispatch funnel** that gives `PlatformError::DispatchError { fn_name }`
its first live construction site, retiring the lone remaining suite skip
(`tests/platform_errors.rs::platform_dispatch_error_carries_fn_name`).

### 9a.1 The problem — an unguarded foreign call

`PlatformError::DispatchError { fn_name, cause, location }` is **defined**
(`crates/cranelisp-types/src/error.rs:261`, with `Display` + `location()` arms) but has
**no live construction site** — only a `#[cfg(test)]` Display unit test
(`crates/cranelisp-platform/src/lib.rs:1761`) ever builds one. The reason: a platform
function is dispatched as an **IO Effect thunk**, and the trampoline invokes it with no
fault guard.

The concrete flow (verified against source):

1. A platform fn (e.g. `shapes::rectangle_area`) returns `CLIO::effect(move || …)`
   (`platforms/shapes/src/lib.rs`; **all** platform fns MUST return `IO _` per FIXME 0318 —
   foreign purity is unverifiable, so foreign work is always sequenced through the
   trampoline). `CLIO::effect_on_resource` (`lib.rs:679`) boxes the closure into a
   `Box<Box<dyn FnOnce() -> i64>>` and writes its raw pointer into an `IO_TAG_EFFECT` node.
   (This §9a narrative is the S81 *design-time* problem statement; the node was 24 bytes
   `[tag | thunk_ptr | resource_token]` at the time. **As-built (ABI v5) the node is 32 bytes**
   — `[tag | thunk_ptr | resource_token | fn_name]` per §5 — the funnel's node-widening (Option A)
   landed.)
2. The intrinsics IO trampoline (`crates/cranelisp-intrinsics/src/io.rs:192`) forces the
   node: `let result = unsafe { cranelisp_platform::call_effect_thunk(thunk_ptr) };`.
   `call_effect_thunk` (`lib.rs:707`) reclaims the box and invokes the closure **directly,
   unguarded**.
3. A fault inside foreign code — a Rust panic, or a hardware trap (SIGSEGV / SIGFPE / SIGILL
   / SIGBUS) — therefore either unwinds through `extern "C"` frames (UB) or kills the
   process. There is **no path that converts a dispatch-time fault into a structured
   `DispatchError`** the user can read.

This is the gap the funnel closes. It is genuine new runtime-feature work, not a defect — a
sanctioned ignore today (S80 user ruling).

### 9a.2 Precedent — `invoke_jit_protected`

The host already runs foreign-ish (JIT-emitted) code under a fault guard at the **macro
expansion boundary**: `src/expander.rs::invoke_jit_protected` (`expander.rs:494`). Its shape
is the template for the funnel:

- a `catch_unwind(AssertUnwindSafe(…))` wrapper catches **Rust panics** (e.g. the
  `runtime_panic` intrinsic's panic on a `match` exhaustiveness failure);
- inside it, `sigsetjmp` saves a recovery point and `install_signal_handlers` arms
  SIGFPE/SIGILL/SIGBUS handlers that `siglongjmp` back without unwinding through C frames;
- after the call, it reads the thread-local error slot via
  `cranelisp_intrinsics::panic::take_runtime_error()` to surface a `runtime_panic`-set message;
- it composes a structured error (today `CranelispError::MacroError { message, location }`),
  mapping the signal number to a human cause string.

The error-slot machinery the funnel needs is **already in place**:
`cranelisp_intrinsics::panic::{take_runtime_error, set_runtime_error}` both exist
(`panic.rs:69`/`:81` — `set_runtime_error` landed as the fork-join ferry companion). The
funnel reuses `take_runtime_error()` exactly as `invoke_jit_protected` does.

### 9a.3 Where the guard sits — the trampoline call site (one boundary, not the combinator)

**The guard wraps the `call_effect_thunk` invocation in the IO trampoline**
(`crates/cranelisp-intrinsics/src/io.rs:192`), **not** `call_effect_thunk` itself and **not**
each platform fn. Rationale (cites Principle 7 — single source of truth; Principle 6 —
complexity budget):

- The trampoline is the **single** site where every platform Effect is forced. One guard
  there covers every platform fn in every mode (`--run`, REPL, `--link`), with no per-fn or
  per-DLL code (mirrors the §1 "no mode fork in the platform's own code" property). Guarding
  inside each platform fn would scatter the guard across every out-of-tree DLL and defeat the
  point.
- `call_effect_thunk` stays a thin `Box::from_raw` + invoke (`lib.rs:707`) — it is the
  reclaim primitive, and a `cranelisp-platform`-resident sigsetjmp/signal-handler install is
  the wrong layer (platform is the contract crate, owns no runtime cadence — §1). The guard
  belongs with the runtime cadence host: **`cranelisp-intrinsics`** (the IO trampoline's
  home; BC §4b — the trampoline is intrinsics-owned).

This placement is the **/arch ruling the implementation needs**, and it is **not yet ruled in
`design/arch/`** — there is no Phase-3 dispatch-funnel FIXME or BC text covering it. The
guard's home crate (intrinsics) and the fn-name plumbing (below) **cross the
platform/int/intrinsics boundary**, so the placement + construction/surfacing path is an
`/arch` call. This design recommends the placement above; **a FIXME `target: /arch` is filed
this pass** (see §13) to ratify it before `/dev` implements, per the cross-component-handoff
rule (root `CLAUDE.md` §"Cross-Skill Changes").

### 9a.4 The fn-name plumbing — the cross-component crux

`DispatchError` carries `fn_name: Symbol` (the offending platform fn, e.g. `area`). **The
trampoline does not have it.** The Effect node is `[tag | thunk_ptr | resource_token]` — the
closure is opaque, and the trampoline's own comment (`io.rs:169-183`) records exactly this:
*"At the trampoline site we do not have a back-reference to the symbol."* This is the load
-bearing difficulty of the feature and the reason it spans three components. Two candidate
plumbing paths, with a recommendation:

**Option A — widen the Effect node with a fn-name coordinate (recommended).** Add a fourth
field to the `IO_TAG_EFFECT` node: a pointer/handle identifying the producing platform fn
(an interned `Symbol` pointer, or an index into a host-side name table). `CLIO::effect` has no
fn-name in scope, so the **producer of the name is the dispatch arm, not the platform fn**:
the value the platform fn returns is an `IO` node whose Effect thunk the *host* created the
call to. The cleanest source of the name is the **call site** — when JIT-emitted code calls a
`DefKind::PlatformEffect` fn (backend GOT-indirect arm, BC §3), the symbol is statically known
at codegen. The backend could bake the fn-name (as a relocated `&'static` `Symbol`/string
pointer, the same family as the trace `DisplayDescriptor` data symbol) and the construction
that builds the Effect node would stamp it into the new field. **Cost:** an Effect-node layout
change → `ABI_VERSION` bump (3 → 4; cheap pre-1.0 per §"q-callbacks-shrinkage"), and a
backend codegen touch. **Benefit:** the name travels with the node to the exact trampoline
site that faults — no correlation, no thread-local.

**Option B — a thread-local "current platform fn" set at the dispatch arm.** The backend's
GOT-indirect platform-call arm (or the int-side dispatch path) pushes the fn-name onto a
thread-local immediately before the call returns the IO node, and the trampoline reads it when
forcing an Effect. **Cost:** fragile — the IO node may be forced far from where it was
produced (Bind chains, Par scheduling defer the force), so the thread-local is stale by the
time the trampoline runs. **Rejected** unless Option A proves to need an ABI bump the user
declines; recorded for completeness.

**The cross-component split (Option A):**

| Component | Owns | Work |
|---|---|---|
| `/platform` (this crate) | the Effect-node layout + `CLIO::effect*` + the `shapes-dispatch-fail` test-DLL fixture | add the fn-name field to the `IO_TAG_EFFECT` node + `CLIO::effect*`; `ABI_VERSION` 3→4; author the fault-injecting fixture DLL |
| `/dev int` (or `/backend`) | the dispatch call site + the trampoline guard | bake/stamp the fn-name at the `DefKind::PlatformEffect` dispatch arm; wrap `call_effect_thunk` in the trampoline with the `invoke_jit_protected`-style guard; construct `PlatformError::DispatchError { fn_name, cause, location }` on fault; surface via `CranelispError::Platform` |
| `/qa` | the e2e | un-ignore `platform_dispatch_error_carries_fn_name`; re-point at the real carrier |
| `/arch` | the boundary ruling | ratify guard placement (intrinsics trampoline) + the fn-name plumbing (Option A node-widen) + the construction/surfacing path |

> **NOTE — the guard host (intrinsics) cannot name `PlatformError`.** `cranelisp-intrinsics`
> depends only on `cranelisp-types` + `cranelisp-platform` (BC §4b). `PlatformError` lives in
> `cranelisp-types` (Decision 0042) — so intrinsics **can** name it. But intrinsics is
> diagnostics-free by charter (it produces runtime semantics, not error-reporting). The clean
> split: the trampoline guard **captures the fault** (signal number / panic payload / slot
> message) + the fn-name and returns a *fault outcome* (a small intrinsics-internal struct or
> a sentinel + slot write via `set_runtime_error`), and **int composes the
> `PlatformError::DispatchError`** at the point it already surfaces runtime errors to the
> user (the `Sess::format_error` / IO-run boundary). This keeps construction in int (the
> diagnostics owner) and the guard mechanism in intrinsics (the cadence owner) — the same
> two-layer split `invoke_jit_protected` uses (intrinsics sets the slot; int reads + composes).
> **This is the precise boundary `/arch` must ratify.**

### 9a.5 The cause string

`DispatchError.cause` is a human string. The funnel maps the fault to it, mirroring
`invoke_jit_protected`'s signal→string table:

- Rust panic caught by `catch_unwind` → the downcast payload string (or "unknown");
- `runtime_panic`-set slot message (via `take_runtime_error()`) → that message;
- SIGFPE → "arithmetic exception (division by zero)"; SIGILL → "illegal instruction";
  SIGBUS → "bus error"; SIGSEGV → "segmentation fault"; other → "signal N".

`location` is the `(platform <name>)` / call-site span — the same `ErrorLocation` the other
`PlatformError` variants carry (Decision 0042). The dispatch arm has the call-site span
statically (it is the IO-producing call's span).

### 9a.6 `--link` parity

The funnel works in `--link` (a standalone executable has no live session but DOES run the
intrinsics IO trampoline — the trace family already proves intrinsics force-links into the
exe-bundle, BC §3). The guard is plain intrinsics runtime code, force-linked like every other
intrinsic; the fn-name baked at codegen survives into the `.o` (same data-symbol family as the
trace descriptor + the platform GOT). So `area` faulting in a `--link`ed binary surfaces the
same structured `DispatchError` — required for the §"q-callbacks" all-modes invariant and the
0289 item-5 e2e (which the design runs through `--run`; the e2e may extend to `--link`).

### 9a.7 The test-DLL fixture (`/platform`-owned)

The e2e needs a platform fn that **faults at dispatch**. `/platform` authors a
`shapes-dispatch-fail` test-DLL (a sibling of `platforms/shapes`, added to the
`tests/scripts/build-link-prereqs.sh` prereq build per `tests/CLAUDE.md`) whose `area` fn's
Effect thunk deliberately faults — the cleanest fault is a Rust `panic!` inside the thunk (caught
by the guard's `catch_unwind`), or a deliberate null-deref (caught by the SIGSEGV handler). The
fixture asserts NOTHING itself (the prior fixture's self-describing stderr was a fake-green,
removed S80) — the e2e observes the host's structured carrier. The fixture reuses the `shapes`
schema/`Rectangle` machinery so the round-trip up to the fault is real.

### 9a.8 Effort + risk

- **Effort:** medium-to-large. The guard mechanism is a near-copy of `invoke_jit_protected`
  (well-understood); the fn-name plumbing (Option A node-widen + backend bake) is the
  substantive part and the `/arch` ratification gate. Flagged Phase-2 as "the likeliest
  single-item slip" — genuine-zero-skips is a **stretch goal**, not a hard gate.
- **Public-API impact:** `cranelisp-platform` baseline regen (the `CLIO::effect*` signature /
  Effect-node ABI change + `ABI_VERSION` 3→4); possibly `cranelisp-intrinsics` (if a fault
  -outcome type surfaces) and `cranelisp-types` is **unchanged** (`DispatchError` already
  exists). The two-update discipline (regen baseline + the surface narrative) applies to the
  platform + intrinsics crates touched.
- **Risk:** the sigsetjmp/signal-handler interaction with the **fork-join error-slot ferry**
  (BC §4b invariant 13) — both touch the thread-local error slot. The design must confirm the
  guard's `take_runtime_error()` read does not race the ferry's `set_runtime_error` on a Par
  /lenient worker. Because platform Effects are forced on the trampoline's own thread (the
  trampoline is the joining thread; structured fork-join joins inside its dynamic extent),
  this is the same own-thread-slot-reader property the ferry already relies on — **flag for
  the implementer to confirm**, not believed to be a new hazard.

---

## 10. Quality attributes

Stewardship per `/design`'s charter; observed against the current source. Untouched-this-pass attributes are noted as such.

| Attribute | Assessment |
|---|---|
| **Simplicity** | Strong. Three files, ~2,800 source lines (much of it rustdoc — appropriate for a contract crate where rustdoc IS the facade); no internal cadence; no session-coordinated state beyond three per-DLL write-once globals (`GLOBAL_ALLOC`, `GLOBAL_ALLOC_WITH_TAG` — `AtomicPtr`; `GLOBAL_SCHEMA` — `OnceLock`). The crate's purpose is "stable contract"; complexity is naturally bounded by the C-ABI surface. Principle 6 (complexity has a budget) is upheld — the crate carries only the marshaling / manifest / ADT types the spec demands. The audit notes `lib.rs` (~1,779 source) is the crate's monolith and the `declare_platform!`/`__declare_platform_body!`/`extract_layout_hash` macro group (~330 lines) is the natural extraction candidate (MED-4 — `/dev` follow-up, §13). |
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
| 42 | `PlatformError` is `cranelisp-types`-hosted with `ErrorLocation` per variant | **Landed.** `manifest_to_descriptors` + `int`'s DLL load path surface `PlatformError` (`LoadFailed`/`AbiVersionMismatch`/`LayoutHashMismatch`/`DispatchError`), not bare `String`. `PlatformError` re-exported here per Principle 15 external-audience exception. (FIXME 0104 absorbed into the S76–S81 landing.) |

### Legacy — embodied (and environmental)

| # | Decision | Bearing on platform |
|---|---|---|
| 10 (environmental) | Base-pointer ABI | Captures rejected interior-pointer alternative; layout convention this crate honours via `HEAP_HEADER_SIZE` |
| 11 (legacy — embodied) | Embedded `drop_glue_ptr` in heap closures | Forward-commitment — Decision 31 callback row uses this layout |
| 13 (legacy — embodied) | Atomic RC `SeqCst` from Ring 1 | `CLHeap::inc_rc` / `dec_rc` use `SeqCst`, NOT `Relaxed` |
| 24 (legacy — embodied) | Uniform consuming calling convention | `CLOwned::into_owned_consuming` (no-inc-on-wrap, dec-on-drop) is the platform-side enactment |
| 26 (legacy — embodied, partly superseded) | `scheduling_class` on `PlatformEffect { … }` | Scheduling-class placement holds; the `platform_fn_ptr`-on-`ModuleEntry::Def` half is **superseded** by GOT-indirect dispatch (S76–S80; `got_slot` on the callable `DefKind` per Principle 20, S83). This crate provides the typed primitives + emits the GOT. |
| 38 (legacy — embodied) | `SharedState` formal definition; `kept_dlls: DashMap<PathBuf, Arc<DllHandle>>`; `Introspection` placement | DLL handles live in `int`; this crate is `kept_dlls`-shape-agnostic |
| 39 (legacy — embodied) | Per-defn source on `Introspection`; `ErrorLocation` carrying coordinates | Errors raised through the platform load path carry `ErrorLocation` once Decision 42 adoption lands |

**Principles cited.** Principle 6 (complexity budget — §10), Principle 7 (single source of truth — §3 divergence #3), Principle 13 (RC `SeqCst` — §10), Principle 14 (FFI layout discipline — §6), Principle 15 (external-audience exception — §1, §2).

---

## 12. Subordinate docs

The other `design/platform/` documents:

| Doc | Status | Disposition |
|---|---|---|
| `CLAUDE.md` | Current | **Keep**. Local conventions for `/platform` design work — read first when designing. |
| `sprint71-redesign.md` | Current | **Keep**. The S71 platform-boundary redesign (schema parser, `CLAdt<T>`, marker-type pattern, `HostCallbacks` growth, `ABI_VERSION = 2`, R1 wired-or-panic gate). The boundary the S76 host-wiring (`host-wiring-s76.md`) wires up. |
| `host-wiring-s76.md` | Current (Phase 3) | **Keep**. The S76 W-Integrate host-wiring plan: platform-side completeness audit (round-trip path), the cross-crate seam map (FIXMEs 0229–0235 → owning crate + data/ABI contract), round-trip completion sequence, and the one /arch seam (S-PLAT-1 schema-literal exposure, FIXME 0250). Platform's own delta is near-zero — the wiring is overwhelmingly consumer-side. |
| `poll-support.md` | Current (S96 Chunk A, pre-implementation) | **Keep**. The `concurrency`-gated `poll_support` ergonomics-suite design (typed env accessor `PollEnv`, fd/timer `Reactor` scaffold, `PollState` phase scaffold) + the web/stdio poll-shape adoption + a two-macro convergence skeleton (`declare_platform!` + the since-**deleted** `declare_concurrent_platform!`) honouring gate (c) — **note:** that two-macro convergence was later superseded by the single-ABI cutover to ONE `declare_platform!` macro (poll-support.md carries its own superseding banners). Evidence-first: the extraction target the Chunk-A `/dev` hand-rewrite converges to. Cites reactor.md §2.8 (acquire-around-poll / RAII Permit) + io-trampoline §12 (poll-node bake) as referenced seams. |
| `platform-dlls.md` | **Refreshed S96 (FIXME 0461 drain).** The capacity carrier (`effect_on_resource_with_capacity` + `IO_EFFECT_CAPACITY_OFFSET`), the ABI-v7 stamp, the namespaced manifest export, the `PlatformError` error surface (Decision 42), and the `pool-demo` blocking test leaf are now reconciled. The mechanics it documents (search path, manifest format, capture-RC protocol, `cranelisp-stdio` reference platform, `cranelisp-test-capture` test platform) remain current and load-bearing. **Keep.** Canonical constructor/constant surface is still the source rustdoc + `io-trampoline.md` §13 — this doc carries the loading mechanics narrative. |
| `archive/platform-registry-removal.md` | Work has landed (Decision 27 deletion + cache-restore addendum). Lessons folded into Decisions 26, 27, 38 and into this master + `platform-dlls.md`. **Archived** to `design/platform/archive/` (FIXME 0106 resolved). |
| `runtime.md` | **Mis-located.** This file is the runtime crate's design doc, not platform's. It collides namewise with `design/runtime/runtime.md` (the canonical home post-S64) and predates the per-crate-master-design baseline. **Delete.** The canonical runtime master is `design/runtime/runtime.md`; nothing in `design/platform/runtime.md` is uniquely load-bearing for the platform crate (the platform-side view of the IO trampoline contract is captured in §5 of this doc; the `call_effect_thunk` semantics in §5; the allocator wiring in §4; the platform-runtime pairing in the §10 Decision register row for Decision 40). Deletion executed this pass — git history preserves content per S64 methodology rule. |

---

## 13. Open questions / FIXMEs filed this pass

### S96 Chunk-B pass (2026-06-29, `/design` platform + /port perspective) — FIXME 0465 (web connection-handle interface)

Resolved **FIXME 0465** (the Chunk-B keystone — the web capacity-on-poll connection
model needed a concrete cranelisp connection-handle interface that did not exist). The
resolution is **`poll-support.md` §3.5** (new): the `web/Listener` + `web/Connection`
handle ADTs (ordinary `.cl` types, /port-owned), the four v8 poll-leaf signatures
(`bind-listener` blocking + `accept-conn`/`read-conn`/`send-conn` poll `ResourceSerial`,
each riding the leading-pair `(token, capacity)` convention), the `.cl` destructuring
wrappers (the cranelisp value SOURCE — `accept`/`read`/`send` destructure the handle and
supply the leading pair so `main.cl` reads in handle terms), and the serial serve-loop
reshape with the Chunk-B launch-and-continue fan-out drop-in seam. The `(token, capacity)`
reach the poll node via the wrapper-placed leading operands → backend bake (offsets 32/40)
→ `await_poll_node` → the A3 acquire-around-poll permit (lit up on every web leaf). §3.5
also **refined §3.2/§3.4.5's loose "capacity N per connection" wording** to the arch §16
faithful model: fresh per-connection token at capacity **1** (serial within the
connection), with the in-flight-**connection-COUNT** ceiling `N` enforced by the **Chunk-B
slice-4 global admission budget** (sibling `/design` intrinsics), NOT a per-connection
capacity-N. **FIXME 0465 deleted this pass.**

**No new FIXME filed; no `/arch` escalation.** The interface uses only the ratified §8.1
leading-pair carrier + ordinary `.cl` ADTs — **no `cranelisp-types` change, no new
cross-crate convention.** One **coordination note for `/sprint`** (recorded in §3.5.6, not
a blocker, no contradiction with the sibling seam): the server demo's "N concurrent
connections; (N+1)th parks" acceptance is a **Chunk-B** property (the global admission
budget the sibling owns), not a Chunk-A per-token-permit property — Chunk A lights the
permit up on every leaf; Chunk B supplies the count ceiling. The rejected shared-pool-token
alternative (which would make the per-token permit bound the count in Chunk A) is recorded
in §3.5.6 with its arch-§16 divergence rationale.

> **Doc-staleness residual (not 0465, flagged for a future `/design` platform pass):**
> `poll-support.md` §2/§4 + `platform-dlls.md` still describe the v6/v7 *coexistence*
> envelope (`#[cfg(feature = "concurrency")]`, ABI-v7, the two-macro split). The S96
> **single-ABI v8 cutover** (A4c — landed) superseded that. A top banner + a §4 banner were
> added to `poll-support.md` to redirect readers; a full v8 sweep of §2/§4 + `platform-dlls.md`
> (ABI 7→8, one `declare_platform!`, ungated ABI types, always-present reactor) is owed but
> out of 0465's narrow scope.

### S96 Chunk-A pass (2026-06-28, `/design` platform) — poll_support + web/stdio v7 + FIXME 0461 drain

This pass authored the new subordinate doc **`design/platform/poll-support.md`**
(the `concurrency`-gated `poll_support` ergonomics suite + the web/stdio v7
poll-shape adoption + the converged macro skeleton honouring Phase-2 gate (c)) and
**drained FIXME 0461** by reconciling §1/§2/§3/§5/§12 of this master + the
mechanics in `platform-dlls.md` to the live ABI-v7 + capacity-carrier state:
`ABI_VERSION` 5 → 7 (the v6/v7 bumps named), `IO_EFFECT_FN_NAME_OFFSET = 24` +
`IO_EFFECT_CAPACITY_OFFSET = 32` added, `effect_on_resource_with_capacity` added to
the constructor inventory, the 40-byte `IO_TAG_EFFECT` payload noted (append-only),
the `IO_TAG_EFFECT_POLL` reserve recorded, the five-file crate shape + the
`concurrency.rs`/`declare.rs` modules named, and the `platforms/pool-demo` blocking
test leaf mentioned alongside `test-capture`. **FIXME 0461 is deleted this pass.**

**No new FIXME filed.** No cross-crate contradiction found against the sibling
Chunk-A design seams (`reactor.md` §2.8 acquire-around-poll / RAII Permit;
`io-trampoline.md` §12 poll-node bake): the platform side is permit-agnostic and the
`PollEnv` accessor adopts io-trampoline §12.2's result-slot-first offset verbatim.
The one coordination point (result-slot placement) is flagged in `poll-support.md`
§2.1/§3.3 as single-sited, not a contradiction. The v7 contract types + the
capacity carrier are `/arch`-owned at `effect-concurrency.md`/`platform-interface.md`
and were read-only here.

### S84 pass (2026-06-16, `/design` platform) — §3 doc-truth refresh (FIXME 0372 / audit MED-1)

This pass refreshed **§3** to the as-built shape per `audits/platform-2026-06-14.md` MED-1 + FIXME 0372: **3 files / ~3,816 source lines / ABI v5 / GOT-indirect dispatch / ADT marshaling**, replacing the stale "single-file, 940 lines, ABI v1, `derive_jit_name`/`platform_fn_ptr`/`JITBuilder::symbol` dispatch" narrative. §3 and §13 are now **consistent** — the old §3 contradicted the §13 staleness verdicts (0039 says `platform_fn_ptr` is gone; old §3 listed it as live; old §3 claimed `PlatformError` "not yet defined" while it is defined + re-exported). §1/§2/§4/§10 were also de-staled (ABI version, three-file count, GOT dispatch, the three per-DLL globals). Doc-only; no behaviour change. The MED-4 / LOW cosmetic items are recorded as follow-ups below. **FIXME 0372's design intent is discharged by this refresh** (the doc-accuracy half); the `/dev` code residue is carried forward as the items below, filed for a `/dev`(platform) follow-up.

**`/dev`(platform) residue (CODE changes — NOT actioned this pass; out of `/design` scope):**

| Item | Audit | Work |
|---|---|---|
| **R1 gate reframe + `t25` fix** | MED-2 | `crates/cranelisp-platform/src/lib.rs`: rewrite `null_alloc_with_tag`'s panic message + rustdoc (`:436-459`), `HostCallbacks::alloc_with_tag` rustdoc (`:424-433`), and the `HostContext::init` comment to **drop** "not yet wired by the host / host-wiring sprint scope / FIXME 0229 / will be removed" and **reframe** the gate as the *permanent uninitialized-host fallback* ("fires only when no host has called `HostContext::init`; install a synthetic callback via `HostContext::init`"). Update the `t25_null_alloc_with_tag_panic_message_contract` test (`:2334`) in the **same change-set** — it currently pins the stale "FIXME 0229" string and so guards the stale message (a unit test guarding a string that must change). |
| **`declare_platform!` extract** | MED-4 | Extract `declare_platform!` + `__declare_platform_body!` + `extract_layout_hash` (~330 lines) from `lib.rs` into a sibling module (`src/macros.rs` or `src/declare.rs`) — co-locates the three-exports emitter + GOT-emit + layout-hash logic, shrinks `lib.rs` to the type/wrapper/const surface. Opportunistic; `/design`-blessed (the sibling-module precedent is `schema.rs`/`adt.rs`). |
| **`schema.rs` `.unwrap()` hygiene** | LOW-2 | Replace the two guarded `.unwrap()`s (`schema.rs:289`, `:463`) with `.expect("byte present — guarded by the peek above")` or thread the peeked byte. Trivial; bundle with any `schema.rs` touch. |

**`/arch` follow-up (filed this pass):** **FIXME 0374** (`target: /arch`) — correct the BC §5 "owns no runtime state" phrasing to name the three per-DLL write-once globals (audit LOW-1). §1 of this doc is already corrected; BC §5 is `/arch`-owned.

### S81 Phase-3 pass (2026-06-13, `/design` platform) — dispatch funnel design + FIXME staleness sweep

This pass designed the **fault-guarded FFI-dispatch funnel** (new §9a — the substantive S81
platform feature) and verified the platform-component FIXME backlog against current source.

**Filed this pass:** **FIXME 0327** (`target: /arch`) — ratify the dispatch-funnel boundary:
guard placement (intrinsics IO trampoline), fn-name plumbing (Option A — widen the
`IO_TAG_EFFECT` node, baked at the backend `DefKind::PlatformEffect` dispatch arm), and the
two-layer `DispatchError` construction path (intrinsics captures, int composes). Cross-component
ruling gating 0289-item-5. See §9a.

**FIXME staleness verdicts (verified against source — bonus reduction):**

| FIXME | Verdict | Evidence |
|---|---|---|
| **0039** (platform_fn_ptr write-site) | **STALE → close** | The `platform_fn_ptr` field **no longer exists anywhere** (`grep` clean across `src/` + `crates/`). The GOT-indirect model (S76–S80) retired it: dispatch is `got_slot = manifest index` + a GotTable wrapping the dlsym'd GOT (BC §5 invariant 1). The single-vs-two-pass write-site question is moot. |
| **0040** (load_and_register_platform shape + no PlatformRegistry) | **STALE → close** | Both bullets resolved. `load_and_register_platform` exists and writes inline (`src/platform.rs:735`); `PlatformRegistry` is fully deleted — the only surviving refs (`src/worker.rs`, `src/bind_chain_analysis.rs`) are historical comments documenting its removal (G8). |
| **0041** (triage 5 v4_platform failures) | **STALE → close** | No `v4_platform` test file exists (only `v4_pipeline`/`v4_repl_eval`, neither carries platform tests). The 5 failures it triaged are gone. |
| **0238** (`declare_platform!` proc-macro upgrade — eliminate `schema_types:`) | **STALE → close** | The `schema_types:` parallel ident-list arm is **already gone**. The platform-interface landing (S76–S80) replaced the marker-type DSL with `schema: include_str!(...)` (a generated artifact); the macro now has only the `schema:` embed arm + a no-schema arm (`lib.rs:1431`+). There is no ident-list to derive from a literal — `macro_rules!` is sufficient, and the proposed proc-macro crate is unnecessary. The redundancy the FIXME targeted was dissolved, not by a proc-macro, but by removing the declaration arm entirely. |
| **0229** (host-side ADT marshaling residual) | **NEAR-STALE → close on absorb** | The `validate_schema` half is withdrawn (layout-hash gate replaced it; `validate_schema`/`null_validate_schema` retired with `ABI_VERSION` 2→3). The `alloc_with_tag` KEEP is DONE + unit-verified (S76) and live in `load_platform_dll` + the exe-bundle. The residual is only null-callback-cleanup *coordination*, which the platform-interface S76–S80 landing absorbed (no `null_validate_schema` remains; `validate_schema` is gone from `HostCallbacks`). Nothing substantive remains — close once `/int`/`/platform` confirm the null callbacks are deleted (a 1-line verify). |
| **0235** (round-trip DLL e2e) | **SUBSUMED by 0289 → close** | Re-pointed into 0289 (2026-06-07). The round-trip + hash-gate + cache-restore walks now LIVE in `tests/spec_platforms_adt.rs` (`platform_adt_roundtrip_run`/`_link`/`_cache_restore`, `platform_adt_hash_gate_*`). Items 1–4 of 0289 are covered; only item 5 (dispatch funnel) remains. 0235's content is fully absorbed. |
| **0289-item-5** (dispatch funnel e2e) | **OPEN — the headline** | The lone irreducible skip. Designed in §9a; gated on FIXME 0327 (/arch ruling) + the `shapes-dispatch-fail` fixture (/platform) + the int/backend funnel + the /qa un-ignore. |

**Net:** five platform FIXMEs (0039, 0040, 0041, 0238, 0235) are confirmed STALE/SUBSUMED and
recommend close-on-verify; 0229 is near-stale (residual is verify-only); 0289-item-5 is the one
genuine open increment, now designed.

### Historical — S71-era pass (superseded by the S81 sweep above)

This pass files three FIXMEs (filing skill: `/design` (platform)):

| Number | Target | Summary |
|---|---|---|
| 0104 | `/dev` | Adopt `PlatformError` per Decision 42 — refactor `manifest_to_descriptors` and `int::load_platform_dll` to construct `PlatformError` rather than `String`; surface via `CranelispError::Platform`; add `Sess::format_error` arm. Spans `cranelisp-types` (define enum), `cranelisp-platform` (refactor), `int` (refactor + format arm). |
| 0107 | `/dev` | Add `#[non_exhaustive]` to `OwnedPlatformFnDescriptor` (`/arch` resolved Option A — extending Principle 14 to cover both `#[repr(C)]` and `#[repr(transparent)]`; `OwnedPlatformFnDescriptor` is the only public type with no FFI repr annotation and SHOULD carry `#[non_exhaustive]`). |
| 0106 | `/design` (self) | **Resolved.** Archived `platform-registry-removal.md` to `design/platform/archive/` with a one-line README, after cross-check against canonical citations (this master + Decisions 26/27/38). |

**Already-tracked, no new FIXME this pass:**

- FIXME 0101 (`/sprint`) covers the platform audit pass (sequenced after Decision 40 / FIXME 0103 lands).
- FIXME 0103 (`/dev`, runtime + int) covers the `IoObserver` relocation per Decision 40 — affects platform indirectly (the platform-runtime pairing in BC §4) but no platform-crate work.
- The `HostCallbacks` expansion (`rc_inc`, `rc_dec`, `invoke_closure`) is forward-commitment per Decision 31 §9 and is intentionally NOT a FIXME today — it lands when spec §10.10.1 adds the `Fn a b` row.
- The `load_manifest` / `parse_type_sig` placement mismatch (facade names them in platform; implementation places them in `int`) is a minor facade text correction — not a `/dev` change. Deferred without FIXME — `/arch` may opportunistically correct facade text to reflect the BC §5 placement.

---

## Cross-references

- `crates/cranelisp-platform/src/lib.rs` `//!` + per-item `///` rustdoc + `design/arch/bounded-contexts.md` §5 — public-API contract (facade retired S71 Wave 4)
- `design/arch/facades/runtime.md` — runtime's facade (consumes platform's `HostContext` for the IO trampoline; `IoObserver` per Decision 40)
- `crates/cranelisp-types/src/{scheduling,module,error}.rs` rustdoc — `SchedulingClass`, `PlatformSpec`, `ErrorLocation`, `PlatformError` (Decision 42); `design/arch/bounded-contexts.md` §7 for cross-type narrative
- `design/arch/bounded-contexts.md` §5 — Platform bounded context
- `design/arch/principles.md` — architectural principles index (Principles 6, 7, 13, 14, 15 cited above)
- `design/arch/CLAUDE.md` — Decisions index (11, 13, 24, 26, 27, 31, 38, 39, 40, 41, 42 cited above)
- `design/platform/platform-dlls.md` — DLL loading mechanics (subordinate; refresh deferred to FIXME 0104 sprint)
- `design/platform/archive/platform-registry-removal.md` — G8 deletion (subordinate; archived per FIXME 0106)
- `crates/cranelisp-platform/src/{lib,schema,adt}.rs` — current implementation (3 files, ~3,816 source lines, ABI v5); `audits/platform-2026-06-14.md` for the structural snapshot
- `src/platform.rs` — `int`'s platform load + path resolution + type signature parser (the integration-side enactment of this crate's contract)
