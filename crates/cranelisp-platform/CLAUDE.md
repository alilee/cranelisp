# cranelisp-platform — local conventions

The voice of the code: FFI/ABI marshalling gotchas, heap-layout invariants, the
`declare_platform!` three-exports contract, schema/layout-hash discipline, and the
submodule seam map. This crate is the C-ABI ground-truth between the host binary
and every platform DLL; it depends only on `cranelisp-types` (no `libloading` —
DLL open/retention is `int`-side). Owned by `/dev` when narrow-deployed here.

## Two host allocators, TWO DIFFERENT return conventions (marshalling trap)

`HostCallbacks` carries two allocators (`lib.rs:597`), and they do NOT agree on
what they return:

- **`alloc(size) -> i64`** returns the **payload pointer** (`base + 16`). Every
  scalar/string/IO constructor subtracts `HEAP_HEADER_SIZE` to recover the base
  before storing it: `CLString::from` (`lib.rs:1207`), `CLIO::pure` (`lib.rs:923`),
  `CLIO::effect_on_resource_with_capacity` (`lib.rs:1036`) all do `payload - HEAP_HEADER_SIZE`.
- **`alloc_with_tag(tag, n, fields) -> i64`** returns the **alloc BASE** already
  (`lib.rs:621` rustdoc step 5). `CLAdt::construct` (`adt.rs:216`) passes the result
  straight into `from_raw` with **no subtraction** — the local is misleadingly named
  `payload_ptr` but is the base. Do not "fix" it by subtracting 16; that double-offsets.

All heap `CL*` wrappers store **base pointers** (address of the
`[total_size i64][rc i64][payload…]` header), never payload pointers (Decision 0013;
`CLHeap` rustdoc `lib.rs:1216`). `inc_rc`/`dec_rc` read RC at `base + 8`; `as_str`/
`read_field`/`read_tag` add `HEAP_HEADER_SIZE` (16) to reach payload.

## ABI_VERSION is the single layout-discipline gate (Principle 14)

`ABI_VERSION` (currently **9**, `lib.rs:298`) is the only host↔DLL compatibility
mechanism — there is no `#[non_exhaustive]` on any `#[repr(C)]`/`#[repr(transparent)]`
boundary type (they are exempt; a field change IS a breaking change → bump). The
bump-rule enumeration lives in the `ABI_VERSION` rustdoc; read it before touching any
layout. **History caveat**: the numeric version and the doc "v4 async-leaf" label
diverge — v7 (`lib.rs:252`) is "the ABI-v4 cascade, recorded numerically as 6→7."
Do not read "v4" in effect-concurrency docs as a numeric ABI version.

## Effect-node layout is append-only; offsets never move

The IO Effect node payload is `[tag][thunk_ptr][resource_token][fn_name_handle][capacity]`
= 40 bytes, built by `effect_on_resource_with_capacity` (`lib.rs:1028`). Offsets are
**append-only across every widening** (24→32 FIXME 0327, 32→40 slice-3 S95), so
`IO_EFFECT_RESOURCE_OFFSET`=16, `IO_EFFECT_FN_NAME_OFFSET`=24 (backend stamps this
post-call; DLL inits it **null** — a null handle degrades to `fn_name: "<unknown>"`,
not a crash), `IO_EFFECT_CAPACITY_OFFSET`=32 all stay put. A new field appends; nothing
reorders. Node layout is an **in-process** backend↔intrinsics convention — widening it
is NOT an `ABI_VERSION` bump (host + DLLs rebuild together).

**DLL-local fault catch (FIXME 0327 Option A, `lib.rs:975`).** The `catch_unwind` in
the effect thunk runs INSIDE the DLL (monomorphised at the `CLIO::effect*` call site),
because a DLL statically links its own panic runtime — a foreign unwind reaching the
host's catch aborts. The caught panic returns as an `EffectOutcome` value
(`lib.rs:872`), NOT a thread-local (DLLs have their own thread-locals). Host-side
`call_effect_thunk` (`lib.rs:1057`) merely **forwards** it; it does NO catch of its own.

## IO_TAG_* — which cross the ABI, which do not

`IO_TAG_PURE`(0)/`EFFECT`(1)/`BIND`(2)/`PAR`(3) are the DLL↔host node tags. But
`IO_TAG_EFFECT_POLL`(4, `lib.rs:340`), `IO_TAG_LAUNCH`(5), `IO_TAG_SELECT`(6) are
**host-built and host-interpreted only** — they never cross the platform DLL ABI, so
adding them was NO `ABI_VERSION` bump. Don't assume a new tag needs a bump; check
whether a DLL ever constructs it.

## declare_platform! — the three-exports emitter (declare.rs)

Every DLL invokes `declare_platform!` once. It emits three exports, all suffixed by the
raw `name:` literal (§5.5.5): the GOT `__cranelisp_got_platform_<name>`, the manifest
`cranelisp_platform_manifest_<name>`, and (optional `schema:` arm) `__cranelisp_layout_hash_<name>`.

- **Load-bearing invariant: manifest order IS GOT slot order** (`declare.rs:369` —
  slot `i` ← `functions[i].ptr`; host dispatches GOT-indirect at `got_slot = manifest index`).
  Guarded by `declare.rs::tests::declare_platform_manifest_order_is_got_slot_order`.
- The manifest symbol name has **one source of truth**: `platform_manifest_symbol(name)`
  (`lib.rs:315`). The macro's `concat!` string (`declare.rs:352`) must match it exactly;
  a unit test pins the equality. Use the raw `name:` literal, NOT the `replace('-','_')`
  rlib-filename form.
- Concurrency key per fn is EITHER `scheduling:` (blocking sugar →
  `ConcurrencyDescriptor::from_scheduling_class`) OR `descriptor:` (poll-shape,
  `blocking=0`), lowered by `__platform_concurrency!` (`declare.rs:294`). Optional
  `drop_state:` (poll-leaf teardown) via `__platform_drop_state!`.
- `extract_layout_hash` (`declare.rs:33`) is a `const fn` byte-scanner for the
  `;; layout-hash:` header — matches the EXACT marker (`;; layout-hash:` with the space,
  with the colon); near-misses return `""`, and `""` is tolerated (first-build).

## Schema is a GENERATED artifact, read by name, callback-free

Platforms **do not declare ADTs** (the Sprint 71 marker-type DSL is retired, FIXME 0286).
A DLL embeds the `/platform-schema`-generated artifact via `include_str!`; the macro
parses it once into a per-DLL `Schema` (`schema.rs`) installed as the process-global
`GLOBAL_SCHEMA` (`adt.rs:90`, `OnceLock`). `CLAdt::read_field` (`adt.rs:185`) resolves
`(offset, FieldType)` **by name** and transmutes at the offset — no host round-trip per
read. Only `CLAdt::construct` touches host state (`alloc_with_tag`).

- Field offset rule: u32 tag at payload+0 (+4 pad), field `i` at `8 + i*8`
  (`schema.rs:315`). Sum fields are dot-qualified (`"Some.val"`); a product
  self-qualifier (`"Rectangle.w"`) strips to the bare field (`adt.rs:338`).
- The schema parser **replicates** a tiny S-expr grammar rather than depend on
  `cranelisp-frontend` (would invert the DAG, Principle 3; `schema.rs:54`). Emit
  (backend `generate_schema`) and this parser agree by construction — a parse error
  signals generator/parser drift, not author error.
- Layout-hash gate: the host regenerates the schema from its live tables and compares
  its hash against the DLL's exported `__cranelisp_layout_hash_<name>`. This SUPERSEDED
  the removed `validate_schema` callback (FIXME 0288) — do not re-add a validation callback.

## Uninitialized-host fallbacks are permanent gates, not scaffolds

`get_global_alloc` **panics** if `HostContext::init` hasn't run (`lib.rs:1126`);
`get_host_alloc_with_tag` returns `null_alloc_with_tag` which panics on call
(`lib.rs:638`). These fire only in `cranelisp-platform` unit tests that exercise a
construction path without a wired host — such a test installs a synthetic callback via
`HostContext::init` first (see `declare.rs:571` for the pattern). Do not treat these as
migration TODOs.

## RC ordering is SeqCst, deliberately

`inc_rc`/`dec_rc` use `Ordering::SeqCst` (`lib.rs:1279`/`1297`) to match Cranelift's
`atomic_rmw`. `Relaxed` is **unsound** (dec reorders before field reads → read-after-free).
Don't relax it for "performance."

## Submodule seam map + where each `#[cfg(test)]` lives

| Submodule | Concern | Unit tests |
|---|---|---|
| `lib.rs` | CL* wrappers, `CLIO`, `CLOwned`, `HostContext`, manifest→descriptors, ABI consts | `src/tests.rs` (`mod tests;` at `lib.rs:1653`) |
| `declare.rs` | `declare_platform!` + `extract_layout_hash` | inline `#[cfg(test)] mod tests` (`declare.rs:465`) |
| `schema.rs` | generated-artifact parser + lookups | `src/schema/tests.rs` |
| `adt.rs` | `CLAdt<T>`, `CLTypeWitness`, field-by-name | `src/adt/tests.rs` |
| `concurrency.rs` | host-reactor C-ABI (`HostCtx`/`Waker`/`PollFn`) — pure `#[repr(C)]` | inline `mod tests` (`concurrency.rs:133`) — LAYOUT-STABILITY pins (offset/size/align) |
| `poll_support.rs` | poll-leaf ergonomics (`PollEnv`/`Reactor`/`PollState`) | inline `mod tests` (`poll_support.rs:254`) |

The crate-root `src/tests.rs` is intentionally a **single flat marshaling-boundary file**
(audit-blessed one-concern, S106 — not split per the S101 reorg). Additionally,
`crates/cranelisp-platform/tests/*.rs` are the crate's own **integration** tests
(macro end-to-end expansion, `CLAdt` products/sums, worked examples) — these belong to
this crate, distinct from the project-root `tests/` owned by `/qa`.

## Known asymmetries a reader would misread as bugs

- **`inc_rc`/`dec_rc`, not `rc_inc`/`rc_dec`** — intentional, matches the historical
  `cranelisp-intrinsics` name (audit F5, `lib.rs:1234`); renaming triggers a consumer
  cascade, deferred.
- **`poll_support.rs` module doc still says "concurrency-gated"** (`poll_support.rs:1`)
  — stale phrasing; the `concurrency` feature is RETIRED (single-ABI cutover, S96;
  `Cargo.toml` has no `[features]`). The suite is CORE/ungated per `lib.rs:159`.
- **`HostContext` has no `Default`, `CLOwned` no `into_inner`, `CLType` is `to_raw`-only**
  — deliberate deletions of speculative facade items (audits F1/F2/F7, S67/S71); source
  is authoritative, do not re-add.
