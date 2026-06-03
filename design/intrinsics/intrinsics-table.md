# `INTRINSICS_TABLE` — the published flat Import-catalog (S76 W-Enablement)

**Status.** Phase 3 design — DESIGN ONLY (no source edits). Feeds /dev (intrinsics) Phase 4/5.

**Author.** `/design (intrinsics)`, 2026-06-03.

**Reads.** `design/arch/bounded-contexts.md` §4b (esp. invariant 11, invariant 9, the §"What crosses the boundary" Outward clause); `sprints/SPRINT.md` §"W-Enablement" + the Phase-2 Architecture review Q1/Q2 + Public-API impact §; `crates/cranelisp-intrinsics/src/lib.rs` crate-root `//!`; `crates/cranelisp-backend/src/jit.rs` (`IntrinsicSymbol`, `intrinsic_symbols()`, `register_intrinsics`, `declare_intrinsics_generic`); `src/worker.rs:3545` (cache-hit reader); `src/session_v4.rs::int_intrinsics()`; `design/arch/CLAUDE.md` Decision 0048 + baseline-diff discipline.

> **Scope note.** This is a subordinate topic doc, not the intrinsics master. The crate has no `design/intrinsics/intrinsics.md` master today — the canonical surface is the crate-root `//!` rustdoc (facade retired S74 W3 per BC §4b §"Per-surface documentation"). This doc elaborates the **one** S76 W-Enablement addition to that surface: `pub static INTRINSICS_TABLE`. It does not restate the whole crate; it pins the table's shape, contents source, consumer contract, ABI guardrail, and test placement so /dev can implement against acceptance criteria.

---

## 1. What is being added, and why now

BC §4b invariant 11 target-states `cranelisp_intrinsics::INTRINSICS_TABLE`: a **published flat `name → (signature, ptr)` catalog** that intrinsics owns and self-publishes — the Decision-0048-for-intrinsics forward commitment (applying the `primitives::PRIMITIVES_TABLE` precedent to intrinsics). Verified **it does not exist in source today** (`grep INTRINSICS_TABLE crates/cranelisp-intrinsics/` → no matches). The catalog's data lives today in backend, as `cranelisp_backend::jit::intrinsic_symbols() -> Vec<IntrinsicSymbol>` (now `pub(crate)`, S75 W3 narrow), enumerated by Rust path (`cranelisp_intrinsics::alloc::heap_alloc as *const u8`, …).

BC §4b invariant 11 says "implementation S77". **The S76 user scope decision (2026-06-02, "INCLUDE ALL" — `sprints/SPRINT.md` §W-Enablement) pulled it forward into S76**, paired with backend's `Jit::new(symbol_tables)` collapse. The Phase-2 /arch review (`sprints/SPRINT.md` §"Public-API impact" item 2) confirms: *"`INTRINSICS_TABLE` needs a NEW published surface on `cranelisp-intrinsics` — yes … `/dev (intrinsics)` authors `pub static INTRINSICS_TABLE` … its baseline + crate-root `//!` rustdoc are the canonical surface … approved here as target-stated by BC §4b inv 11."*

The motive is the **single-JIT-setup boundary** (BC §3): `Jit::new(symbol_tables)` derives the entire JIT symbol set from one source — GOT data symbols from `symbol_tables`, and **intrinsic Import targets from `INTRINSICS_TABLE`**. Today the enumeration is by Rust path inside backend, which requires backend to name `cranelisp_intrinsics::*` Rust paths in `intrinsic_symbols()`. Moving the catalog's *home* to intrinsics makes the crate self-describing and lets backend (and int's cache-hit / `--link` paths) read one published table instead of three divergent enumerations.

**Single-source-of-truth (Principle 7).** The catalog moves to its natural owner: intrinsics knows its own externs. `backend::IntrinsicSymbol` / `intrinsic_symbols()` retire as a *public* concept (they were already `pub(crate)`); backend becomes a *reader* of `INTRINSICS_TABLE`, not the owner. The transitional `intrinsic_symbols()` reader is deleted once the readers switch (see §5).

---

## 2. Shape of `INTRINSICS_TABLE`

### 2.1 Record type — `IntrinsicEntry`

The current `backend::IntrinsicSymbol` is the data the catalog must carry. It is the **alignment target** for the entry record (SPRINT W-Enablement: *"align with the existing `IntrinsicSymbol`/`intrinsic_symbols()` data already in the crate"*). Field-by-field disposition:

| `IntrinsicSymbol` field | Carry into `IntrinsicEntry`? | Rationale |
|---|---|---|
| `name: &'static str` | **Yes** — the catalog key + the emitted-call ABI string (§4 guardrail). | |
| `ptr: *const u8` | **Yes** — the registered fn pointer; the `JITBuilder::symbol(name, ptr)` / `Linker::register_symbol(name, ptr)` second arg. | |
| `param_count: usize` | **Yes** — drives `declare_intrinsics_generic`'s signature loop (`for _ in 0..param_count { sig.params.push(I64) }`). | |
| `has_return: bool` | **Yes** — drives the same fn's `if has_return { sig.returns.push(I64) }`. | |
| `is_runtime: bool` | **Yes** — carry it. It encodes the `runtime/` vs user-visible-name split. **No functional consumer today** (verified: only `#[allow(dead_code)]` on the backend field, no read). But the backend field rustdoc (jit.rs:96-101) explicitly keeps it *because* the S77/S76 catalog target needs the runtime-vs-primitive split it encodes; dropping it would churn every construction site twice. Keep it on the entry; document it as classificatory metadata, not dispatch input. |

Proposed record (target-stated; /dev authors):

```rust
/// One backend-emitted-call target in the published intrinsics catalog.
///
/// The `signature` half of BC §4b invariant 11's `name → (signature, ptr)` is
/// expressed as the `(param_count, has_return)` pair — every intrinsic param
/// and return is `i64` at the ABI (heap pointers cross as integers, invariant
/// 10 / the value-passing C-ABI), so the Cranelift signature is fully
/// determined by the arity + return-ness. No `cranelisp-types` type is named
/// (invariant 10 — no `FQTypeName`/`TypeName` at the surface).
pub struct IntrinsicEntry {
    /// Emitted-call ABI string (the `#[export_name]`/`#[no_mangle]` linker
    /// symbol the backend emits `Linkage::Import` against). LOAD-BEARING: §6
    /// guardrail — this MUST equal the per-module extern's export name.
    pub name: &'static str,
    /// Function pointer to the Rust implementation in this crate.
    pub ptr: *const u8,
    /// Count of `i64` parameters (Cranelift signature param loop).
    pub param_count: usize,
    /// Whether the fn returns an `i64` (false = void).
    pub has_return: bool,
    /// `runtime/`-prefixed infrastructure (true) vs user-visible-named
    /// backend-emitted target (false). Classificatory only — no dispatch
    /// consumer. Retained per the catalog-design need (jit.rs:96-101).
    pub is_runtime: bool,
}
```

**`signature` interpretation (answering SPRINT's "what `signature` type").** The BC's `(signature, ptr)` "signature" is **not** a `cranelisp-types` `Type`/`Scheme` and must NOT become one — invariant 10 forbids `FQTypeName`/`TypeName` at the intrinsics surface, and the value-passing C-ABI (invariant 9/the §"Window types" value-passing clause) is uniformly `i64`-in / `i64`-or-void-out. The signature is therefore the **`(param_count, has_return)` pair**, exactly what `declare_intrinsics_generic` already consumes. This is the minimum mechanism (Principle 6 / Principle 2 narrow interface) — a richer typed signature would add a `cranelisp-types` dependency at the surface for zero codegen gain. **Flag for /arch:** none — no new `cranelisp-types` type is needed; the entry is self-contained `&'static str` + raw ptr + two scalars. (Confirms the Phase-2 review's "no other cross-crate interface types are needed.")

### 2.2 Static shape — `pub static INTRINSICS_TABLE: &[IntrinsicEntry]`

Mirror the `PRIMITIVES_TABLE` precedent's *publication* (a `pub static` the crate owns, read by consumers) but **NOT** its *structure*. CRUCIAL ASYMMETRY (BC §4b invariant 11): `PRIMITIVES_TABLE` is a `SymbolTable` + `Arc<GotTable>` mounted into the session's `SymbolTables` map (primitives ride the GOT-indirect path); `INTRINSICS_TABLE` is a **flat catalog, Import-dispatched, never mounted, never GOT-slotted, consumed only at three resolution points, never at codegen** (invariant 11). So the shape is the simplest thing that carries the records:

```rust
/// The published flat Import-catalog of this crate's backend-emitted-call
/// targets (BC §4b invariant 11 — Decision-0048-for-intrinsics).
///
/// Flat `name → (signature, ptr)`. NOT a mounted GOT-module (contrast
/// `cranelisp_primitives::PRIMITIVES_TABLE`): intrinsics are Import-dispatched
/// (invariant 9) — not a module, no `SymbolTable`, no GOT slots. Consumed at
/// THREE resolution points, never at codegen: (a) JIT construct
/// (`Jit::new(symbol_tables)` → `JITBuilder::symbol`), (b) cache-hit load
/// (`Linker::register_symbol`), (c) `--link` (names resolved against the
/// archive). See the crate-root `//!` and BC §4b invariant 11.
pub static INTRINSICS_TABLE: &[IntrinsicEntry] = &[ /* … 15 entries … */ ];
```

A `&'static [IntrinsicEntry]` slice (not a `Vec`, not a `LazyLock<HashMap>`) is the right shape:
- The contents are compile-time constant (fn pointers are const-evaluable as `… as *const u8` in a static initializer).
- Consumers iterate (`for e in INTRINSICS_TABLE`) — no keyed lookup is needed at any of the three resolution points (all three register *every* entry unconditionally; forbidden-patterns clause 1 — no conditional registration). A slice is cheaper than a map and matches the existing `Vec`-iteration consumer shape.
- It is `Sync` (a `&'static` slice of records whose only non-`Sync` field is `*const u8`; raw pointers are `!Send`/`!Sync`, so **the static needs a `Send + Sync` justification**). See §2.3.

### 2.3 `Send`/`Sync` for the raw-pointer-bearing static

`*const u8` is `!Send + !Sync`, so `static INTRINSICS_TABLE: &[IntrinsicEntry]` does not auto-derive `Sync` and a bare `static` of a non-`Sync` type is rejected. Two viable mechanisms; /dev picks:

1. **Wrapper newtype with `unsafe impl Sync`** — `struct IntrinsicCatalog(&'static [IntrinsicEntry]); unsafe impl Sync for IntrinsicCatalog {}` then `pub static INTRINSICS_TABLE: IntrinsicCatalog = …`. Safety justification: the pointers are static fn addresses, never written, valid for the whole process — sharing `&` across threads is sound. Parallels the existing pattern intrinsics/platform use for process-global fn-ptr state (`HostContext`'s `AtomicPtr`, `PlatformFn`'s explicit `unsafe impl Send + Sync`, BC §5 invariant 6).
2. **`fn intrinsics_table() -> &'static [IntrinsicEntry]`** returning a function-local `&'static` slice (the slice literal is `'static`; the fn just hands out a shared ref). Avoids the `unsafe impl` entirely — the borrow is produced per-call, no shared static of a `!Sync` type exists. This is the **closest analog to today's `intrinsic_symbols() -> Vec<…>`** and is the lower-friction migration for the readers (they already call a fn).

**Recommendation: option 2 (`pub fn intrinsics_table() -> &'static [IntrinsicEntry]`)** despite the SPRINT/BC wording "`pub static INTRINSICS_TABLE`". Rationale: (a) it sidesteps the `unsafe impl Sync` (Principle 6 — minimum mechanism, no unsafe where a fn suffices); (b) it is a drop-in shape match for the three readers that today call `intrinsic_symbols()`; (c) the baseline still records it as the crate's published catalog surface. **Flag for /arch:** the BC text says "static"; if /arch wants the literal `pub static` (for symmetry with `PRIMITIVES_TABLE`'s static), option 1 + the `unsafe impl Sync` newtype delivers it — this is a naming/shape preference, not a semantic difference, and either satisfies invariant 11. /dev should confirm the chosen spelling against /arch before regen so the baseline + BC wording agree. **This is the one seam to surface to /arch** (see §7).

---

## 3. Contents — source of the entries

The 15 entries are exactly today's `backend::jit::intrinsic_symbols()` set (jit.rs:148-175), **relocated** verbatim (same names, same ptrs, same `param_count`/`has_return`/`is_runtime`), with the ptr expressions now naming **in-crate** Rust paths (e.g. `alloc::heap_alloc as *const u8` instead of `cranelisp_intrinsics::alloc::heap_alloc as *const u8`) since the table lives inside the crate:

| name | in-crate ptr path | params | ret | is_runtime |
|---|---|---|---|---|
| `runtime/alloc` | `alloc::heap_alloc` | 1 | yes | true |
| `runtime/dealloc` | `alloc::heap_dealloc` | 1 | yes | true |
| `runtime/panic` | `panic::runtime_panic` | 2 | yes | true |
| `runtime/rc_underflow_check` | `rc::rc_underflow_check` | 1 | yes | true |
| `runtime/alloc_string` | `heap_string::heap_alloc_string` | 2 | yes | true |
| `runtime/string_read` | `heap_string::string_read` | 1 | yes | true |
| `runtime/vec_new` | `vec_runtime::vec_new` | 1 | yes | true |
| `runtime/vec_drop` | `vec_runtime::vec_drop` | 2 | no | true |
| `runtime/run_io` | `io::cranelisp_run_io` | 1 | yes | true |
| `cranelisp_ivar_create` | `ivar::ivar_create` | 1 | yes | true |
| `cranelisp_ivar_spark` | `ivar::ivar_spark` | 1 | yes | true |
| `cranelisp_ivar_force` | `ivar::ivar_force` | 1 | yes | true |
| `vec-set-copy` | `vec_runtime::vec_set_copy` | 4 | yes | false |
| `vec-push-copy` | `vec_runtime::vec_push_copy` | 3 | yes | false |
| `vec-push-grow` | `vec_runtime::vec_push_grow` | 2 | yes | false |

**Scope boundary — what is NOT in `INTRINSICS_TABLE`:**
- **The 14 int-owned intrinsics** (`session_v4.rs::int_intrinsics()` — `discover-tests`, `run-test`, `cranelisp_trace_format`, the 11 `cranelisp_trace_*`). These are int-hosted (Decision 40 Path B1; `src/CLAUDE.md` §"Int-owned JIT intrinsics") and physically live in `src/`. `INTRINSICS_TABLE` is **the `cranelisp-intrinsics` crate's catalog only**. int continues to register `int_intrinsics()` separately at JIT setup, concatenated with `INTRINSICS_TABLE` by whatever assembles the full JIT symbol set. The catalog does not pretend to be the complete JIT symbol universe — it is intrinsics' published contribution. (This matches the existing split: `intrinsic_symbols()` already excludes the int-owned + trace symbols, jit.rs:171-173.)
- **Primitives** (`add-i64`, `str-concat`, `vec-len`, …) — GOT-dispatched via `PRIMITIVES_TABLE`, never `JITBuilder::symbol`-registered (invariant 9, Decision 0048; the negative-space confirmed by jit.rs:164-167's `vec-len` note).

**Trace symbols deliberately absent** (Decision 40 / Path B1) — preserve the jit.rs:171-173 comment's intent in the table's rustdoc.

---

## 4. Consumer contract

Three resolution points (BC §4b invariant 11 (a)/(b)/(c)). The table publishes; consumers iterate-and-register. None consume it at codegen.

### 4a. Backend — `Jit::new(symbol_tables)` (JIT construct) + `declare_intrinsics_generic`

- **`Jit::new(symbol_tables)`** (the S76 backend collapse, `sprints/SPRINT.md` Public-API impact item 3) registers each entry via `JITBuilder::symbol(e.name, e.ptr)`. This replaces today's `register_intrinsics(builder)` loop over `intrinsic_symbols()` (jit.rs:180-184).
- **`declare_intrinsics_generic<M: Module>`** (jit.rs:733) builds the Cranelift `Import` declaration from each entry's `param_count` + `has_return` (the loop already shown at jit.rs:738-766). It switches from `intrinsic_symbols()` to `cranelisp_intrinsics::intrinsics_table()` / `INTRINSICS_TABLE`. The 6 convenience-accessor `match sym.name` arms (jit.rs:757-764) are unaffected — they key on `e.name`.
- **Backend reads, does not own.** `backend::IntrinsicSymbol` + `intrinsic_symbols()` are deleted (or kept only as a thin `pub(crate)` shim during the same wave, then removed). This is a backend `/dev` edit, not intrinsics'; the intrinsics deliverable is *publishing the table backend reads*. **Contract from intrinsics' side:** the table is iterable, every entry's `name` is the exact emitted-call ABI string, every `ptr` is a valid live fn address for the process lifetime, `param_count`/`has_return` exactly describe the extern's `i64` ABI.

### 4b. int cache-hit — `Linker::register_symbol` (`src/worker.rs:3545`)

Today: `for sym in cranelisp_backend::jit::intrinsic_symbols() { linker.register_symbol(sym.name, sym.ptr); }`. Migrates to: `for e in cranelisp_intrinsics::INTRINSICS_TABLE { linker.register_symbol(e.name, e.ptr); }` (or the `intrinsics_table()` fn form). Same iterate-and-register contract; int now depends on the **intrinsics** crate for this (int already depends on intrinsics — BC §4b dep-edges para — so no new dep edge). This is an int `/dev` edit; the intrinsics deliverable is the readable table.

### 4c. `--link` (exe-bundle)

The `--link` path resolves the same `name` strings against the `cranelisp-intrinsics` static archive (exe.rs:44 — "linked … against the user `.o`s and the runtime/platform archives"). **No code reads `INTRINSICS_TABLE` here** — the linker resolves by symbol name against the archive's `#[export_name]`/`#[no_mangle]` symbols. The table's contract to this path is purely the **name agreement** (§6 guardrail): the catalog's `name` strings MUST equal the archive's exported symbol names, or `--link` gets unresolved-symbol errors. This is the ABI continuity the guardrail protects.

---

## 5. Relation to `intrinsic_symbols()` — the migration shape

| Aspect | Today (S75) | Target (S76 W-Enablement) |
|---|---|---|
| Owner | backend (`jit::intrinsic_symbols()`, `pub(crate)`) | **intrinsics** (`INTRINSICS_TABLE` / `intrinsics_table()`, `pub`) |
| Record type | `backend::jit::IntrinsicSymbol` (`pub(crate)`) | `intrinsics::IntrinsicEntry` (`pub`) |
| Enumeration | by Rust path from backend (`cranelisp_intrinsics::alloc::… as *const u8`) | by in-crate path (`alloc::… as *const u8`) |
| Backend role | owner + sole reader | **reader only** (`declare_intrinsics_generic`, `Jit::new`) |
| int cache-hit reader | reads `backend::intrinsic_symbols()` | reads `intrinsics::INTRINSICS_TABLE` |

**Net:** `backend::IntrinsicSymbol`/`intrinsic_symbols()` retire as concepts; the data, unchanged, relocates to its owner. The §6 ABI is unchanged — same 15 names, same ptrs, same arities (BC §4b invariant 11: *"only the enumeration source moves (Rust-path → published table)"*). This is final-state, not interim (Principle 8): the catalog's home is intrinsics by Decision-0048-for-intrinsics; backend reading its own list was the pre-S76 residual being removed.

**Sequencing (Phase-2 review Q2):** intrinsics publishes `INTRINSICS_TABLE` → backend `Jit::new(symbol_tables)` consumes it → int's two readers (worker.rs:3545 cache-hit; the deleted hand-assembly) switch. Intrinsics' publication lands **with or just before** the backend collapse. The intrinsics edit is independent and can land first (it only adds a static + record type; nothing breaks until the readers switch).

---

## 6. ABI guardrail — the emitted-call name agreement MUST survive

This is the load-bearing invariant the change must not break (SPRINT W-Enablement: *"the §6 emitted-call-ABI guardrail (per-module externs must survive — don't break the `#[export_name]` ABI)"*).

**The invariant.** The backend emits `Linkage::Import` relocations keyed on the **string name** (crate-root `//!` §"How the surface is reached" 1; BC §4b invariant 11 §"unchanged"). That string is the intrinsic's `#[export_name = "…"]` / `#[no_mangle]` linker symbol on the per-module extern fn (e.g. `runtime/alloc`, `vec-push-copy`, `cranelisp_ivar_force`). Three independent things MUST agree on this string:
1. The per-module extern's `#[export_name]` attribute (the `--link` archive symbol).
2. `INTRINSICS_TABLE`'s `name` field (the JIT `JITBuilder::symbol` / cache-hit `Linker::register_symbol` registration name).
3. The name the backend emits the `Import` against (driven by `declare_intrinsics_generic` reading the table's `name`).

**What the change must NOT do.** Authoring `INTRINSICS_TABLE` must NOT touch the per-module `#[export_name]`/`#[no_mangle]` attributes or the per-module `pub` paths. Those stay exactly as they are (crate-root `//!` §"Symbol survival under DCE" / §"How the surface is reached" — the per-module `pub` paths are fn-ptr-harvested + the export names emit the linker symbols independent of Rust visibility). The table **references** the same fns (`alloc::heap_alloc as *const u8`) and **republishes** their already-established names — it adds a publication surface, it does not redefine the ABI. The DCE-survival mechanism (FIXME 0247 — `#[export_name]` emits the symbol; no `#[used]` static needed) is untouched: the table holds fn *pointers* (a Rust-path reference that also keeps the symbol live via the harvest), orthogonal to the export-name attribute.

**Guardrail check for /dev + /qa.** A unit test asserting the table's names exactly match the historically-registered set is the durable guard (see §8). Because the names are the ABI, a typo in a table `name` is an unresolved-symbol crash at JIT finalize or `--link`, not a compile error — so the test must compare the literal strings, and ideally cross-check that each `name` resolves (the `ptr` is non-null and the fn is the expected one). The forbidden-patterns clause 1 (no conditional registration) reinforces: every entry registers unconditionally; the test asserts the **full** set is present.

---

## 7. Seam for /arch

**One seam, naming/shape only — no new `cranelisp-types` type.** BC §4b invariant 11 + `sprints/SPRINT.md` say "`pub static INTRINSICS_TABLE`". §2.3 recommends `pub fn intrinsics_table() -> &'static [IntrinsicEntry]` to avoid an `unsafe impl Sync` on a raw-pointer-bearing static (Principle 6). Both satisfy invariant 11 (a published, iterable, flat `name → (signature, ptr)` catalog read at the three resolution points); the difference is `static` + `unsafe impl Sync` newtype vs `fn` returning `&'static [..]`. **/dev should confirm the spelling with /arch before baseline regen** so the `public-api.txt` baseline, the crate-root `//!`, and BC §4b invariant 11's "static" wording agree. If /arch holds to the literal `static`, /design defaults to /arch's wording (the BC is the configuration that grounds this surface; `feedback_hold_to_facade_default` — on a naming choice with a Decision/BC statement either way, hold to the stated wording). **No FIXME filed** — this is a Phase-3 confirmation the /dev wave resolves with /arch directly; flagging it here per the deliverable.

Confirmed **no** other /arch seam: the `signature` half is the `(param_count, has_return)` scalar pair (§2.1), not a `cranelisp-types` `Type` — invariant 10 forbids `FQTypeName`/`TypeName` at this surface, and the value-passing C-ABI is uniformly `i64`. The Phase-2 review already confirmed "no other cross-crate interface types are needed."

---

## 8. Baseline + rustdoc + test placement

**Baseline + rustdoc (the canonical surface; facade retired S74).** Per baseline-diff discipline (`design/arch/CLAUDE.md` §"Baseline-diff discipline") and `feedback_retired_facade_drops_compliance`: the crate's surface IS the source — `public-api.txt` baseline + compiler = definition, rustdoc = rationale. The /dev change-set MUST, in the same commit:
1. **Regenerate** `crates/cranelisp-intrinsics/public-api.txt` via `cargo public-api --omit blanket-impls,auto-derived-impls -p cranelisp-intrinsics > crates/cranelisp-intrinsics/public-api.txt`. The diff adds `IntrinsicEntry` (struct + 5 fields) + `INTRINSICS_TABLE` (or `intrinsics_table`). The raw-ptr field means `IntrinsicEntry` auto-projects `!Send + !Sync` — the baseline records this (auto-trait impls are KEPT per the discipline, a real semver signal); if option-1's `unsafe impl Sync` newtype is used, the baseline records that `Sync` impl too.
2. **Update the crate-root `//!`** (`crates/cranelisp-intrinsics/src/lib.rs`) — add a section documenting `INTRINSICS_TABLE` as the published flat Import-catalog: its three resolution points, the asymmetry-vs-`PRIMITIVES_TABLE` (flat, not mounted), the relation to the retired `backend::intrinsic_symbols()`, and the §6 name-agreement ABI. Per-item `///` on `IntrinsicEntry` + each field, and on the static/fn (the §2 rustdoc drafts are the starting text). This is the canonical rationale surface — there is no `facades/intrinsics.md` to update (retired S74 W3).
3. **No BC edit** — BC §4b invariant 11 already target-states the table (verified). The only BC wording to reconcile is "static" vs the recommended fn form (§7), and that is /arch's call on its own file, via the §7 confirmation — /design does not edit BC.

**Unit-test placement (`/dev` owns; per `feedback_unit_tests_with_dev` + `project_test_strategy`).** Unit tests live inside `crates/cranelisp-intrinsics/src/` (a `#[cfg(test)] mod tests` next to the table — likely `lib.rs` or a small `catalog.rs` if the table gets its own module). Tests the /dev wave should author:
- **Name-set completeness** — assert the table contains exactly the 15 expected names (the §3 set), no more, no fewer (catches accidental add/drop; the ABI guardrail's positive+negative coverage — wrong items absent, all expected present).
- **Non-null ptrs** — assert every entry's `ptr` is non-null (catches a mis-pathed fn reference at the const-eval site).
- **Arity sanity** — assert the `(param_count, has_return)` for each name matches the historical `declare_intrinsics_generic` expectation (e.g. `runtime/vec_drop` has `has_return: false`, `vec-set-copy` has `param_count: 4`). This is the signature half of the catalog; a wrong arity is a JIT signature mismatch (silent miscompile or trap), so it needs a guard.
- **`is_runtime` classification** — assert the `runtime/`-prefixed names are `is_runtime: true` and the user-visible-named ones (`vec-*-copy`, `vec-push-grow`) are `false`, documenting the (currently consumer-less) classification's intent.

**Cross-crate integration coverage (/qa, `tests/`).** The end-to-end guard that `INTRINSICS_TABLE` correctly drives JIT setup is the existing e2e suite passing once `Jit::new(symbol_tables)` reads the table (any program that allocates, uses strings/vecs, or runs IO exercises the registration). No new int-level integration test is strictly required for the table itself — but per the SPRINT W-e2e directive, if an e2e failure traces to a missing/mis-named intrinsic registration, the assessment "would a unit test inside the crate have caught this?" points back to the §8 name-set/arity tests. Flag any such gap to /qa.

---

## 9. Quality-attribute stewardship (S76 touch)

| Attribute | This sprint |
|---|---|
| **Simplicity** (P6) | The table is the minimum mechanism — a flat slice of plain records, `(param_count, has_return)` not a typed signature; recommended `fn` form avoids `unsafe impl Sync`. No accretion. |
| **Maintainability** | Single source of truth (P7): the catalog moves to its owner; backend stops naming intrinsics' Rust paths; one place to add/remove an intrinsic (the table + the per-module extern). |
| **Observability** | A mis-registered intrinsic surfaces today as a JIT-finalize panic / `--link` unresolved-symbol — opaque. The §8 name-set/arity unit tests move that failure to a fast, legible test signal. |
| **Concurrency-safety** | The `Send`/`Sync` question (§2.3) is the only concurrency dimension — the table is read-only static fn-ptr data; the recommended fn form needs no `unsafe`, the static form needs a justified `unsafe impl Sync` paralleling `HostContext`/`PlatformFn`. |
| **Performance** | Untouched — registration is once-per-session; a 15-entry slice iteration is negligible. No pathological case. |
| **Testability** (P5) | Structural: the table is a pure data value testable in isolation inside the crate; no session construction needed (`project_test_strategy` — unit tests live in `src/`). |

---

## 10. /dev acceptance checklist (Phase 4/5 hand-off)

1. `pub` catalog published on `cranelisp-intrinsics` — `IntrinsicEntry` record + `INTRINSICS_TABLE` static (or `intrinsics_table()` fn per §7 /arch confirmation), 15 entries per §3, in-crate ptr paths.
2. `Send`/`Sync` resolved per §2.3 (recommended: fn form; else `unsafe impl Sync` newtype with the §2.3 safety justification).
3. Per-module `#[export_name]`/`#[no_mangle]` attributes + `pub` paths **untouched** — §6 ABI guardrail held; the table republishes names, does not redefine them.
4. `public-api.txt` regenerated + crate-root `//!` updated in the same commit (§8); no `facades/intrinsics.md` (retired), no BC edit (target-stated).
5. Unit tests in `src/` per §8 (name-set completeness, non-null ptrs, arity sanity, `is_runtime` classification).
6. Backend (`declare_intrinsics_generic`, `Jit::new`) + int (`worker.rs:3545`) reader switches are **separate /dev waves** (backend, int) — this crate's deliverable is the readable table; sequence per §5.
7. /arch spelling confirmation (§7) closed before baseline regen.
