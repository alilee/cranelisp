# Platform host-wiring — Sprint 76 (W-Integrate)

**Owner**: `/design` (cranelisp-platform narrow deployment).
**Date**: 2026-06-03.
**Status**: PHASE 3 DESIGN.
**Scope**: The platform crate's own part of the S76 host-wiring set (FIXMEs 0229–0235), the cross-crate seam map, and the round-trip completion plan. Companion to `design/platform/sprint71-redesign.md` (which built the boundary this sprint wires) and `design/platform/platform.md` (master).

**Inputs grounding this doc**: `sprints/SPRINT.md` §W-Integrate + Phase-2 Architecture review §Q3; `design/arch/bounded-contexts.md` §5 (esp. §"Future host-wiring story" + invariants 1/4/5); FIXMEs `0229`–`0235`; `crates/cranelisp-platform/src/{lib,adt,schema}.rs` (the landed S71 boundary); `src/platform.rs` (`load_platform_dll`, `register_platform_in_tc`, `parse_platform_type_sig`); `crates/cranelisp-exe-bundle/src/lib.rs:97-106` (the `--link` HostCallbacks init); `crates/cranelisp-intrinsics/src/alloc.rs` (the allocator the wired `alloc_with_tag` builds on).

---

## 1. Executive summary — what S71 left, what S76 wires

The S71 redesign (`sprint71-redesign.md`) built the **entire platform-side boundary** and it is **landed and green**:

- `crates/cranelisp-platform/src/schema.rs` (956 LOC) — the S-expr schema parser, `Schema`/`TypeShape`/`Variant`/`Field`/`FieldType`/`SchemaParseError`, `lookup_field_offset` + `lookup_variant_field_offset`.
- `crates/cranelisp-platform/src/adt.rs` (626 LOC) — `CLAdt<T>`, `CLAdtType`, `AnyAdt`, `GetSchema`, `read_tag`/`read_field`/`own_field`/`construct`/`into_typed`, the type-witness check, dot-qualified sum lookup.
- `crates/cranelisp-platform/src/lib.rs` — `HostCallbacks` grown to three fields (`alloc`, `alloc_with_tag`, `validate_schema`); `ABI_VERSION = 2`; the named-null callbacks `null_alloc_with_tag` (R1-gate panic) + `null_validate_schema` (returns 0); the `GLOBAL_ALLOC_WITH_TAG` runtime path (`get_host_alloc_with_tag`); `HostContext::init` stores `alloc_with_tag` into `GLOBAL_ALLOC_WITH_TAG`; the `declare_platform!` `schema:` arm.

**S71 deferred only the host wiring** — the two named-null callbacks in `HostCallbacks` are still pointed at the placeholders at *both* construction sites (`src/platform.rs:189` JIT path; `crates/cranelisp-exe-bundle/src/lib.rs:101` `--link` path). The R1 gate is therefore active: `CLAdt::construct` panics, and `validate_schema` is permissive (returns 0, no cross-check).

**The decisive finding for /design (platform): the platform crate's own S76 work is essentially zero new code.** The host-wiring set is overwhelmingly *consumer-side* (int/frontend/typecheck/backend/repl/qa). The platform crate's role is:

1. **Confirm the runtime path is complete** (it is — §2).
2. **Possibly relocate the `alloc_with_tag` *contract implementation*** — but per BC §5 invariant 4 ("string layout owned by intrinsics; intrinsics is the post-runtime-split host") and FIXME 0229 step 1, the **wired** `alloc_with_tag` body belongs in `cranelisp-intrinsics`, NOT in `cranelisp-platform`. Platform stays state-free per BC §5. So even this is a seam, not platform-crate work.
3. **Hold the schema-validation runtime contract** (`null_validate_schema` is the gate; the wired validator is int-side, FIXME 0231/0229-step-2).
4. **Drop the named-null callbacks** once the host wires real ones (FIXME 0229 step 4) — but that deletion is *triggered by* int's wiring and lands in int's change-set as the gate removal; platform's only act is the deletion of the two `pub extern "C" fn`s + their tests, which is a `/dev (platform)` follow-on after int wires.

**Conclusion: there is no platform-crate-side *host integration* to author.** The S71 boundary already exposes everything the host needs (`Schema::parse`, `CLAdt::*`, the `alloc_with_tag` signature contract, `get_host_alloc_with_tag` runtime resolution). The round-trip is gated entirely on the cross-crate seams. This doc therefore (a) confirms the platform side is complete, (b) maps the seams to their owning crates with the data/ABI contract at each, (c) names the round-trip completion sequence, (d) flags the one seam that needs an /arch ruling (the `alloc_with_tag` ABI shared with int 0229).

---

## 2. Platform-side completeness audit — the round-trip path

The full round-trip is: **declare** (schema in `declare_platform!`) → **DLL** (compiled marker types + `LazyLock<Schema>`) → **load** (host reads manifest + schema) → **call** (cranelisp source calls a platform fn taking `CLAdt<T>`) → **marshal back** (platform fn reads fields / constructs a result, crosses the FFI as `i64`).

Walking each segment against the landed source:

| Segment | Platform-side mechanism | State | Gating seam (if any) |
|---|---|---|---|
| **declare** | `declare_platform!` `schema:` arm parses type names at expand time, emits marker structs + `CLAdtType`/`GetSchema` impls + `LazyLock<Schema>` (`Schema::parse` at first access). | **Complete** (S71). | none |
| **DLL → load (manifest)** | `manifest_to_descriptors` UTF-8-validates + returns `OwnedPlatformFnDescriptor`s. | **Complete.** | none |
| **load → schema capture** | The schema literal is embedded by the macro; the host must capture it for caching (FIXME 0232) + validation (0229-step-2). **The macro does NOT currently expose the schema literal on the manifest** — it parses it into the DLL-local `LazyLock`, but the host has no manifest field carrying the raw text. | **GAP — see §3, seam S-PLAT-1.** | 0232 (cache), 0229-step-2 (validate) both need the schema text host-side. |
| **load → sig typecheck** | `PlatformFn.type_sig` carries `"(Fn [Rectangle] Int)"`; the host parses it. Today int's `parse_platform_type_sig` (`src/platform.rs:308`) is ad-hoc and cannot resolve schema-declared ADT names. | host-side; **gated** on 0230/0231/0233. | 0230, 0231, 0233 |
| **call → field read** | `CLAdt::read_field` / `read_tag` / `own_field` — callback-free, DLL-local schema lookup + transmute. | **Complete + unit-tested** (adt.rs T9–T13). | none |
| **call → construct** | `CLAdt::construct` → `get_host_alloc_with_tag()` → `alloc_with_tag(tag, n, ptr)`. The runtime resolution path is complete; the callback is `null_alloc_with_tag` until wired. | path **complete**; callback **gated**. | 0229-step-1 (intrinsics impl + int wires it) |
| **marshal back** | construct returns `CLOwned<CLAdt<T>>` (alloc base, RC=1, no re-inc); the i64 crosses back. | **Complete** (relies on wired `alloc_with_tag`). | 0229-step-1 |

**The `alloc_with_tag` contract (the heap layout the wired callback must produce)** is fully pinned in `HostCallbacks::alloc_with_tag` rustdoc + FIXME 0229 step 1:

```
total_size = 16 (HeapHeader) + 8 (tag u32 + 4 pad) + 8 * field_count
[total_size: i64][rc: i64 = 1]            ; HeapHeader (offset 0/8)
[tag: u32][pad: u32]                       ; payload + 0
[field_0: i64][field_1: i64]...            ; payload + 8, + 16, ...
return: alloc BASE pointer (NOT payload)   ; matches CLString convention
```

`CLAdt::from_raw` stores the base; `read_tag`/`read_field` add `HEAP_HEADER_SIZE` to reach the payload. This contract is **consistent with `cranelisp-intrinsics::alloc::alloc_with_rc`** (writes `[total_size][rc=1]` header, returns base) — so the wired `cranelisp_alloc_with_tag` is a thin wrapper: `alloc_with_rc(8 + 8*field_count)` then write tag+pad+fields, return base. **No platform-crate change required** for this; it is intrinsics work consumed by int's wiring.

**Verdict: the platform-side round-trip path is complete except for one genuine platform-touching gap — the schema literal is not exposed for host capture (S-PLAT-1).** Everything else is consumer-side seams.

---

## 3. The one platform-touching seam — schema literal exposure (S-PLAT-1)

FIXME 0232 (cache) and FIXME 0229-step-2 (validate) both require the **host** to obtain the raw schema text. Today:

- The macro parses the schema *only* into a DLL-local `LazyLock<Schema>` static; it is not on the manifest.
- `PlatformManifest` (`#[repr(C)]`, ABI-governed) has no `schema_*` field.

There are two candidate resolutions; **this is the seam that needs an /arch ruling** because it touches the `#[repr(C)]` ABI boundary (and thus `ABI_VERSION`) which is /arch-governed cross-crate territory, AND it shares the host-side ADT-marshaling data contract with int 0229.

### Option A — add `schema_ptr: *const u8` + `schema_len: usize` to `PlatformManifest`

The macro writes the raw schema literal (already a `&'static str`) into two new manifest fields; `manifest_to_descriptors` surfaces it as `schema_literal: String` on the returned tuple (or a new `OwnedPlatformManifest.schema_literal` field).

- **Cost**: `#[repr(C)]` layout change → `ABI_VERSION` bump (2 → 3) per the bump rules. **But S71 already bumped 1 → 2 for the `HostCallbacks` growth this same arc** — a second bump in the immediately-following sprint for a field S71 could have included is a process smell. Mitigation: this is the host-wiring sprint S71 explicitly deferred; the bump is the honest signal that the on-disk/on-wire ABI grew.
- **Pro**: the schema travels with the manifest exactly as the macro authored it; no re-derivation; the host has the literal at load with zero extra mechanism. Symmetric with how `type_sig` strings already ride the manifest.
- **Con**: two ABI bumps in two sprints; the manifest grows a variable-length payload (pointer+len, like the existing `type_sig` length-prefixed strings — so actually consistent with the existing `PlatformFn` shape).

### Option B — `validate_schema` callback already carries the literal; reconstruct for cache from `Schema`

The `validate_schema` callback signature **already takes `schema_ptr`/`schema_len`** (`lib.rs:394`) — so the macro must *already* be passing the schema literal to that callback at DLL init. Confirm: does the macro call `validate_schema(schema_ptr, schema_len, ...)` at init?

- If **yes**, the host already receives the literal through the validate callback at load; FIXME 0232's cache field can be populated from that same call (host stashes the bytes it was handed). No manifest field, no ABI bump. The macro change (if any) is to ensure the `schema:` literal flows into the `validate_schema` invocation — which the S71 callback signature was *designed* for.
- If **no** (the macro emits the callback field but never invokes it at init), then S71 left the *invocation* unwired too, and the host-wiring sprint adds the macro-side init call. That is a **platform-crate change** (`declare_platform!` emits a `HOST.callbacks().validate_schema(SCHEMA_TEXT.as_ptr(), SCHEMA_TEXT.len(), ...)` call in the manifest extern).

**Recommendation to /arch**: prefer **Option B** — it requires **no ABI bump** (the `validate_schema` field already exists post-S71) and keeps the schema text flowing through the channel S71 already designed for it (the validate callback's `schema_ptr`/`schema_len` params). The cache literal (0232) is captured host-side from the same bytes. Option A's manifest growth is only justified if the schema must be available *before* the validate callback fires (it is not — validation IS the first host touch of the schema). The platform-crate delta under Option B is small and bounded: ensure `declare_platform!` invokes `validate_schema` at init with the embedded literal (verify against the landed macro; author the call if missing).

**This doc does not rule** — it is `/arch`'s call (ABI boundary + shared with int 0229). Flagged in §6.

---

## 4. Cross-crate seam map (FIXME → crate → data/ABI contract)

The host-wiring set spans six crates + qa. Platform owns none of the bodies below except the S-PLAT-1 macro touch (§3, pending /arch). For each seam: the owning `/design`+`/dev`, the data crossing, and platform's dependency on it.

| FIXME | Owner | Seam | Data / ABI contract at the seam | Platform's stake |
|---|---|---|---|---|
| **0229-step-1** | `/dev (intrinsics)` impl + `/dev (int)` wire | `cranelisp_alloc_with_tag` body in intrinsics; int writes the fn ptr into `HostCallbacks.alloc_with_tag` at **both** sites (`src/platform.rs:189`, `exe-bundle/src/lib.rs:101`). | `extern "C" fn(tag: u32, field_count: u32, fields_ptr: *const i64) -> i64`; produces the heap layout in §2; returns alloc base. Built on `intrinsics::alloc::alloc_with_rc`. | Consumes platform's `HostCallbacks::alloc_with_tag` signature + the layout contract (already pinned in rustdoc). Removes the R1 gate. |
| **0229-step-2** | `/dev (int)` | Host `validate_schema` implementation: re-parse via `cranelisp_platform::Schema::parse`, cross-check declared type-names against the typecheck symbol-table, write diagnostic to the `err_msg` buffer, return non-zero on mismatch. | `extern "C" fn(schema_ptr, schema_len, err_msg_ptr, err_msg_capacity, err_msg_len_out: *mut usize) -> i32` (0 ok). Consumes `Schema::parse` + typecheck symbol-table. | Consumes platform's `Schema::parse` (public) + the `validate_schema` signature. Replaces `null_validate_schema`. |
| **0229-step-4** | `/dev (platform)` follow-on | Delete `null_alloc_with_tag` + `null_validate_schema` + their tests once both wired. | n/a (deletion). | **Platform-crate change** — but triggered by int's wiring; lands after 0229-step-1/2. Baseline regen (the two `pub extern "C" fn`s leave the surface — and `ABI_VERSION` does NOT change; the callbacks are not ABI struct fields, they are the *default values* the host stops using). |
| **0230** | `/frontend` | `pub fn parse_type_expr(src, source_id) -> Result<TypeExpr, ...>` — parse one type-expr S-expr. | String in → `TypeExpr` out (single expression, not a program form). | Indirect — int uses it to parse `PlatformFn.type_sig`; platform supplies the sig string, frontend parses it. Replaces platform's role of "just hand the string to int". |
| **0231** | `/typecheck` | `pub fn check_type_expr(expr, ctx, symbol_tables) -> Result<Type, CheckError>` — typecheck a standalone type-expr against a symbol-table. | `TypeExpr` + `CheckContext` + `SymbolTables` in → resolved `Type` out; resolves schema-declared ADT names. | Indirect — enables sig types to reference schema ADTs (`(Fn [Rectangle] Int)`); also the path 0229-step-2's validator uses. |
| **0232** | `/backend` | `.meta.json` gains `schema_literal: String` (optional, `""` for schema-less DLLs). | JSON string field; round-trips the raw schema text for cache-restore re-parse + re-validate. | Consumes the schema literal (per S-PLAT-1 resolution — whichever channel /arch picks supplies it). |
| **0233** | `/int` | Remove `parse_platform_type_sig`; route sigs through 0230+0231; register platforms as **normal modules** with their own `SymbolTable` + `GotTable` (BC §5 invariant 1 target: synthetic `platform.<name>` module, DLL retained on `SymbolTable.dll`). | `ModuleEntry::Def` per fn (`kind: DefKind::PlatformEffect { scheduling_class }`, `got_slot`, `scheme`); DLL handle on the platform module's `SymbolTable.dll: Option<D>`. | Consumes `manifest_to_descriptors` output; retires int's call to it as a *bespoke* path in favour of the module-loader path. Platform's `OwnedPlatformFnDescriptor` surface unchanged. |
| **0234** | `/repl` | `/abi <TypeName>` emitter — cranelisp `deftype` → schema-DSL text per `sprint71-redesign.md §1` BNF + §1.3 poly naming. | Reads symbol-table; emits `(TypeName ((CLInt x) ...))`. Reserves CL-wrapper names (`Int`→`CLInt`). | Pure consumer of the schema-DSL grammar platform settled (§1 of sprint71-redesign). No platform-crate change; the grammar is the contract. |
| **0235** | `/qa` | Round-trip e2e: `platforms/test-adt/` DLL + `tests/spec_platforms_adt.rs` (construct/read/list-sum), cache-restore round-trip, schema-typo mismatch rejection. | Exercises the whole §2 round-trip end-to-end. | The **acceptance criterion** for the platform e2e gate. Platform supplies the DLL-author surface (`declare_platform!` schema arm + `CLAdt`); qa builds the fixture DLL against it. |

### Seam ownership summary (which FIXME → which crate)

- **Platform crate**: 0229-step-4 (delete null callbacks, follow-on) + the S-PLAT-1 macro touch *if* /arch picks Option A or the "macro doesn't yet invoke validate_schema" branch of Option B. Otherwise **zero platform-crate code**.
- **intrinsics**: 0229-step-1 body.
- **int**: 0229-step-1 wiring (both sites) + 0229-step-2 validator + 0233 (the largest item).
- **frontend**: 0230.
- **typecheck**: 0231.
- **backend**: 0232.
- **repl**: 0234.
- **qa**: 0235.

---

## 5. Round-trip completion plan + sequencing

Per the Phase-2 review §Q3, the platform wave lands **after** the int W-Absorb cascade defines the host surface. Within the wave, the ordering the data dependencies force:

1. **0230 (frontend `parse_type_expr`) + 0231 (typecheck `check_type_expr`)** — upstream producers; the sig-parsing path and the validator both consume them. Land first / in parallel (different crates).
2. **0229-step-1 (intrinsics `cranelisp_alloc_with_tag`)** — independent of 1; can land in parallel. Thin wrapper over `alloc_with_rc`.
3. **S-PLAT-1 resolution (/arch ruling) → schema literal exposure** — gates 0232 + 0229-step-2. Resolve the ruling before 0232/validator land. If Option B and the macro already invokes `validate_schema`, this is a no-op confirmation.
4. **0229 int wiring** — int writes `cranelisp_alloc_with_tag` into both `HostCallbacks` sites (removes R1 gate) + implements the `validate_schema` body (consumes `Schema::parse` + 0231's typecheck path). Sequences after 1+2+3.
5. **0233 (int platform-as-module + `parse_type_sig` removal)** — the largest item; consumes 0230+0231. Lands with/after 0229 wiring (both touch `src/platform.rs`).
6. **0232 (backend `.meta.json` schema_literal)** — consumes the schema-literal channel from S-PLAT-1; needed for cache-restore round-trip.
7. **0229-step-4 (platform deletes null callbacks)** — after int wires real ones at both sites. Platform-crate follow-on; baseline regen.
8. **0234 (repl `/abi`)** — independent ergonomic; can land any time after the grammar (already settled). Not a round-trip gate.
9. **0235 (qa round-trip + mismatch + cache-restore tests)** — the acceptance criterion; lands last, gates `spec_platforms.rs` + `spec_platforms_adt.rs`.

**What gates the platform e2e tests** (`spec_platforms.rs`, `platform_errors.rs`, `spec_08_modules.rs` platform paths, and the new `spec_platforms_adt.rs`):
- **Hard gate**: 0229 wiring (construct un-panics) + 0233 (cranelisp source can name platform-declared ADTs because platforms are real modules) + 0230/0231 (sigs referencing ADTs typecheck).
- **Cache-restore gate**: 0232 + S-PLAT-1 (schema literal survives cache round-trip).
- **Mismatch-rejection gate**: 0229-step-2 (`validate_schema` wired) + 0231 (symbol-table cross-check).
- **Not a gate**: 0234 (`/abi`) is pure ergonomics; 0229-step-4 (null deletion) is cleanup.

---

## 6. Open /arch seams

One seam needs an /arch ruling; one confirmation request.

1. **S-PLAT-1 — schema literal exposure for host capture (REQUIRES /arch ruling).** FIXME 0232 (cache) + 0229-step-2 (validate) need the host to obtain the raw schema text. Option A (new `#[repr(C)]` `PlatformManifest.schema_ptr/_len` fields → `ABI_VERSION` 2→3 bump) vs Option B (reuse the already-present `validate_schema` callback's `schema_ptr`/`schema_len` params; capture host-side; **no ABI bump**). **/design (platform) recommends Option B.** This is /arch's call because it touches the `#[repr(C)]` ABI boundary (/arch-governed) AND the host-side ADT-marshaling data contract shared with int 0229. A `FIXME target: /arch` will be filed for the ruling.

2. **`alloc_with_tag` host-side ADT-marshaling ABI shared with int 0229 (CONFIRM).** The heap layout the wired `cranelisp_alloc_with_tag` must produce (§2) is pinned in `HostCallbacks::alloc_with_tag` rustdoc and consistent with `intrinsics::alloc::alloc_with_rc`. /design (platform) confirms the contract is complete + unambiguous; no /arch *authoring* needed, but the contract is the int↔intrinsics↔platform three-way agreement, so /arch should confirm it as part of approving the 0229 wiring (the layout is already BC §5 invariant 4 territory — "one i64 representation per CLType, agreed between platform and intrinsics").

**Macro confirmation needed before §3 resolves (for /dev, not /arch):** does the landed `declare_platform!` actually *invoke* `validate_schema` at DLL init with the embedded schema literal? This determines whether Option B is a no-op confirmation or a small macro-emission addition. Verified by reading the macro body in `lib.rs` during /dev; flagged here as the pivot for S-PLAT-1.

---

## 7. Testability + coverage implications

- **Platform-crate unit tests** (`adt.rs` T9–T25, schema parser tests, ABI_VERSION=2, R1-gate message) already cover the boundary the host wires *against*. No new platform-crate unit tests are owed by the host-wiring itself — the boundary is unit-tested; the wiring is exercised by qa's e2e (0235).
- **One unit-test gap if S-PLAT-1 resolves to a macro change**: if `declare_platform!` is updated to invoke `validate_schema` at init, a compile-fixture test (sibling to T17–T21 macro-arm fixtures) should assert the macro emits the call. `/dev (platform)` authors it when the macro touch lands; noted for `/qa` awareness.
- **0235 is the durable e2e record** per `feedback_repros_join_suite` — the round-trip, cache-restore, and mismatch-rejection tests join the suite permanently and gate `spec_platforms_adt.rs`.

---

## 8. Quality attributes (this pass)

| Attribute | Assessment |
|---|---|
| **Simplicity** | Upheld (Principle 6). Platform's host-wiring delta is near-zero; the wired bodies live in intrinsics + int where the state/typecheck dependencies belong. Option B (no ABI bump) is the minimum-mechanism resolution for S-PLAT-1. |
| **Maintainability** | The seam map (§4) keeps each FIXME's blast radius in its owning crate. The R1 gate's removal is "two lines at each of two sites" (int) + the named-null deletion (platform follow-on) — clean per Principle 18. |
| **Observability** | The wired `validate_schema` (0229-step-2) is the observability win: schema mismatches surface as DLL-load errors with a diagnostic message + the form span (via `PlatformError`), replacing the current silent permissive `null_validate_schema`. |
| **Concurrency-safety** | Untouched. `GLOBAL_ALLOC_WITH_TAG` is write-once-at-init (`SeqCst`) like `GLOBAL_ALLOC`; the wired `alloc_with_tag` is `extern "C"` over `alloc_with_rc` which is already concurrency-safe (atomic counters). No new shared state. |
| **Performance** | Untouched. `alloc_with_tag` is one allocation + a field memcpy; `validate_schema` runs once per DLL load (sub-millisecond re-parse). No hot path. |
| **Testability** | The boundary is unit-tested (S71); the wiring is e2e-tested (0235). Coverage is structural. |

---

## 9. Next skills

- `/arch` — rule S-PLAT-1 (schema literal exposure: Option A ABI-bump vs Option B reuse-validate-callback; /design recommends B) + confirm the `alloc_with_tag` three-way ABI contract as part of approving 0229. A `FIXME target: /arch` will be filed for the ruling.
- `/dev (intrinsics)` — author `cranelisp_alloc_with_tag` (0229-step-1) over `alloc::alloc_with_rc` per the §2 layout contract.
- `/dev (int)` — wire `alloc_with_tag` at both `HostCallbacks` sites + implement the `validate_schema` body (0229) + platform-as-module + `parse_type_sig` removal (0233). Largest consumer.
- `/dev (frontend)` — `parse_type_expr` (0230); `/dev (typecheck)` — `check_type_expr` (0231); `/dev (backend)` — `.meta.json` schema_literal (0232).
- `/dev (platform)` — delete `null_alloc_with_tag`/`null_validate_schema` + tests (0229-step-4) after int wires; baseline regen. Author the macro `validate_schema`-invocation fixture test if S-PLAT-1 resolves to a macro touch.
- `/repl` — `/abi <TypeName>` (0234); `/qa` — round-trip + cache-restore + mismatch e2e (0235), the platform e2e acceptance criterion.

---

## Cross-references

- `design/platform/sprint71-redesign.md` — the boundary this sprint wires (§1 schema BNF, §3 marker-type, §4 CLAdt API, §5 HostCallbacks growth, §9 R1 gate)
- `design/platform/platform.md` — master crate design (§7 manifest/DLL discovery, §9 forward-commitment)
- `design/arch/bounded-contexts.md` §5 — Platform BC (§"Future host-wiring story", invariants 1/4/5)
- `design/arch/fixmes/0229`–`0235` — the host-wiring set
- `sprints/SPRINT.md` §W-Integrate + Phase-2 review §Q3 — sprint scope + ordering
- `crates/cranelisp-platform/src/{lib,adt,schema}.rs` — landed S71 boundary
- `crates/cranelisp-intrinsics/src/alloc.rs` — `alloc_with_rc` the wired `alloc_with_tag` builds on
- `src/platform.rs` — `load_platform_dll`, `register_platform_in_tc`, `parse_platform_type_sig` (to be removed by 0233)
- `crates/cranelisp-exe-bundle/src/lib.rs:97-106` — the `--link` HostCallbacks init site
