# `cranelisp-primitives` — S87 Stage-B deep audit (delta + currency)

> **Point-in-time assessment (2026-06-20).** `/review` Stage-B pass per
> `sprints/SPRINT.md` → Stage B (7-lens depth model, R5a same-instrument
> requirement). This is a **delta + currency check** on the deep baseline
> `audits/primitives-2026-06-14.md`, *not* a from-zero look. The baseline had
> no standalone `.mmd`; the fresh `audits/cranelisp-primitives-s87-current-state.mmd`
> is the first committed diagram for this crate.
>
> **Scope.** `crates/cranelisp-primitives/src/` (9 files; corrected **956**
> production LOC per `audits/loc-s87.md` — the smallest non-trivial workspace
> surface). READ-ONLY on code; this audit produces findings only.
>
> **As-designed reference.** `bounded-contexts.md` §4a (primitives BC +
> invariants 1–8); Decision 0048 (static `PRIMITIVES_TABLE` + GOT-in-crate +
> backend severance); crate-root `//!` rustdoc (`lib.rs:1-96`). No
> `facades/primitives.md` (retired S74 W3).

## Headline

The crate is in **strong architectural health and has materially improved since
the 2026-06-14 baseline.** The two substantive baseline findings (HIGH-1
heap-offset duplication; MED-1 open-coded RC inc) are both **RESOLVED** — and
resolved *well*, with behaviour-preserving guard tests and `const _` compile-time
assertions, exactly as the baseline remediation plan specified. The S86
`neq-string` defect seed (a never-created primitive) is now closed at the
primitives surface (`string.rs:108` + harvest key `lib.rs:385`). No Blocker, no
new HIGH. Findings below are MED/LOW maintainability polish, concentrated on the
hand-maintained three-edit registration seam (the one place the de-leak /
curated-wrapper exposure narrative (S86 seed) actually bites here).

## Baseline reconciliation (R5a — same-instrument diff)

| Baseline finding | S87 status | Evidence |
|---|---|---|
| **HIGH-1** `marshal.rs` hardcodes heap offsets (`PAYLOAD/FIELD0/FIELD1`, magic `.add(8)`) | **RESOLVED** | `marshal.rs:41-53` now derives all offsets from `HeapHeader::SIZE` + a local `FIELD_STRIDE`, with `const _` asserts; `shallow_rc_inc` routes through `rc::rc_inc` (no magic `8`). Two guard tests added (`heap_offsets_derive_from_heap_header`, `shallow_rc_inc_targets_canonical_rc_field`). Module rustdoc gained the single-source-of-truth note (`marshal.rs:10-20`). |
| **MED-1** two RC-inc disciplines (non-atomic in `marshal`, atomic in `string_identity`) | **RESOLVED** | Both now route through `cranelisp_intrinsics::rc::rc_inc` (`marshal.rs:154-156`, `string.rs:138`). The non-atomic `*rc_ptr += 1` data-race hazard under S85 auto-IO sparks is gone — explicitly called out in `marshal.rs:149-153` rustdoc. |
| **MED-2** `extern_shims()` is a hand-maintained 45-entry registry; omission direction (extern present, harvest key missing) is the residual gap | **STILL OPEN** (now 46 entries) | `lib.rs:340-404`. Verified: all 46 `#[export_name]` externs are present as harvest keys today (manual diff, clean). But the closing test the baseline asked for ("every `#[export_name]` extern is a harvest key") was **not** added — `extern_shims_harvest_covers_full_inventory` still only checks the *forward* direction + a hand-maintained allow-list. See MED-1 below. |
| **MED-3** `marshal.rs` unsafe/complexity hot-spot; raw reads not encapsulated | **PARTIALLY RESOLVED** | Subsumed-by-HIGH-1 hardening landed (offsets now single-sourced, so raw accesses are correct-by-construction against canonical layout). Raw `read_i64`/`write_i64` are still offset-indexed free fns rather than a typed accessor, but the correctness-coupling concern is closed. Downgrade to LOW (see LOW-2). |
| **LOW-1** stale `cranelisp-runtime` / `facades/backend.md` refs in rustdoc | **RESOLVED (S98, FIXME 0493)** | `int.rs`/`float.rs`/`bool.rs`/`operator.rs` migration narrative past-tensed to "the pre-D43 runtime crate"; `ring0.rs` `facades/backend.md` → `bounded-contexts.md` §3. See LOW-1 below. |
| **LOW-2** `vec-get/set/push` carry never-populated GOT slots; rationale only in a comment | **STILL OPEN** | `lib.rs:256-262` documents it well; the three null slots remain invisible to the test suite (no value-position-fallback guard). See LOW-3 below. |

**Counts:** Resolved 2 · Partially-resolved 1 · Still-open 3 (all MED/LOW). **No regressions.** No baseline finding moved *up* in severity.

## 7-lens checklist (SPRINT.md Stage B i–vii)

- **(i) Duplicated code paths / mirrors** — The headline duplication (heap offsets, RC inc) is gone (HIGH-1/MED-1 resolved). One residual structural duplication remains: the **three-coordinated-edits registration seam** (extern body + `#[export_name]` + harvest key + ring-table row). This is the Principle-7 single-source tell the S86 curated-wrapper seed points at — see MED-1. The 46 string-literal `m.insert(...)` rows in `extern_shims()` mirror the 46 `#[export_name = "..."]` attributes one-for-one (`lib.rs:344-401`).
- **(ii) Dead paths** — No `produce_disasm`-class zero-call-site dead code. The only "dead-slot" shape is the intentional 3 null Vec-query GOT slots (LOW-3). `ring0.rs:208-220` is a retired-machinery *comment* block (no code), which is fine but contributes to LOW-1 staleness.
- **(iii) Function-budget overruns** — None. Largest production fn is `quote_sexp_build` (`marshal.rs:253-314`, ~60 lines) and `insert_vec_query_entries` (`lib.rs:267-334`); both well under the ~100-line ceiling. No god functions.
- **(iv) RC-symmetry (consuming-inc uniformity, Decision 24)** — **Clean and now uniform.** Every heap-arg-taking extern consumes the heap args it does not return (`string.rs` all `consume_shallow`; `marshal.rs` `consume_slist`/`consume_sexp`; `int.rs` `parse_int` consumes `s`). RC inc is now single-disciplined through `rc::rc_inc`. The newly-registered `neq_string` (`string.rs:109-116`) correctly consumes both args symmetrically with `str_eq`/`str-concat` — no asymmetry introduced. Scalar ring0 ops take non-heap i64 and correctly do **not** consume. **No finding.**
- **(v) Resolution-seam consolidation** — Single seam: `PRIMITIVES_TABLE` is the one front door; `build_primitives_table()` is the one builder; `extern_shims()` is the one harvest. No second/REPL-vs-batch path. The cross-crate single-resolution-seam question (DEF-1 family) is an `/arch` synthesis concern, not interior to this crate.
- **(vi) Interim-architecture residue (Principle 8)** — No live interim code. Residue is doc-only: stale `cranelisp-runtime`/`facades/backend.md` references narrating a completed migration (LOW-1). The `ring0_jit_symbols()` retirement is fully done (comment-only at `ring0.rs:208-220`).
- **(vii) Cross-crate-boundary / host-callback hygiene (R5b)** — Inward dep on `cranelisp-intrinsics` is the blessed substrate (alloc/rc/drop/heap_string/vec_runtime/panic) and is used consistently; heap-layout consts are single-sourced from `cranelisp-types::HeapHeader` and intrinsics (no local copies, post-HIGH-1). Backend severance (`primitives ⟂ backend`) holds structurally — backend reaches primitives only via the GOT slab symbol. **One boundary nit:** `string.rs:197-210` (`str_split`) hand-rolls raw Vec construction (`DATA_PTR_OFFSET`/`LEN_OFFSET` pointer writes) rather than going through a `vec_runtime` typed setter — the same "hand-roll across the FFI/host boundary what a sibling crate also hand-rolls" class lens vii names. See MED-2.

## Findings

### MED-1: The three-edit primitive-registration seam is still hand-maintained, and the baseline-requested omission-direction guard was not added
**Files**: `crates/cranelisp-primitives/src/lib.rs:340-404` (`extern_shims`), `:824-847` (`extern_shims_harvest_covers_full_inventory`)
**Severity**: Medium (single source of truth — Principle 7; maintenance hazard) · **routes**: `target: /dev`

Adding a primitive still requires three coordinated, name-matched edits: (1) the extern body + `#[unsafe(export_name = "name")]`, (2) a `ring{0,1,3}_primitives()` row (for table-registered prims), and (3) an `m.insert("name", fn as *const u8)` harvest line. The three string literals must match exactly; a typo in the harvest key yields a **null GOT slot at runtime**, not a compile error.

This is precisely the failure-shape the S86 seed flags: the `neq-string` defect was a name that the typecheck dispatch table referenced but no primitive created. The primitives surface is the first place re-export + wrapper-forwarding happens at scale, and the registration seam is where a name can silently fail to materialise. The crate's guard tests catch the *forward* direction (`got_slots_hold_extern_ptrs_for_harvested_shims`, `extern_shims_harvest_covers_full_inventory`) but the **baseline (MED-2) explicitly asked for an omission-direction test** ("assert every `#[export_name]` extern is present as a harvest key") and it was **not added**. The `neq-i64|neq-f64|neq-bool|neq-string|sconcat` allow-list in `extern_shims_harvest_covers_full_inventory` (`lib.rs:842`) is itself a hand-maintained exception set that will accrete (it grew by one — `neq-string` — since the baseline).

I verified manually that all 46 externs are harvested today, so this is **not** a live defect — it is an unguarded seam that the project's own discipline (`memory/feedback_unit_test_per_fix`, failing-not-ignored) says should carry a test.

**Proposed remediation**: Minimum — add the omission-direction test the baseline asked for (a compile-time-or-test assertion that every `#[export_name]` extern fn appears as a harvest key). Stronger (Suggestion-tier) — collapse the three edits to one via a small declarative macro or table that emits the attribute, the harvest entry, and the ring row from one source. The macro is optional; the guard test is the actionable ask.

### MED-2: `str_split` / `str_join` hand-roll raw Vec memory layout instead of using `vec_runtime` typed accessors (lens vii)
**Files**: `crates/cranelisp-primitives/src/string.rs:185-241`
**Severity**: Medium (cross-crate boundary hygiene — R5b lens vii; risk-surface containment) · **routes**: `target: /dev` (with `/arch` cross-ref if `vec_runtime` needs a setter)

`str_split` allocates a Vec via `cranelisp_intrinsics::vec_runtime::vec_new(count)` (good — the blessed allocator) but then writes the data pointer and length **by hand** with raw offset arithmetic:

```rust
let data_ptr = *((vec_base as *const u8).add(DATA_PTR_OFFSET) as *const *mut i64);
for (i, part) in parts.iter().enumerate() { *data_ptr.add(i) = heap_str; }
*((vec_base as *mut u8).add(LEN_OFFSET) as *mut i64) = count;
```

`str_join` (`string.rs:222-225`) symmetrically hand-reads the same layout. This is the lens-vii class: primitives hand-rolls Vec element-store/len-set that `cranelisp-intrinsics::vec_runtime` is the owner of. The offsets are correctly single-sourced (imported consts, post-HIGH-1), so this is **not** a duplicate-offset defect — but the *write discipline* (where the len is set relative to element population, whether a store path is RC-aware) lives in two crates. `vec_runtime` already owns `vec_set_copy`/`vec_push_copy`; a `vec_runtime`-side "build a Vec<String> from a slice" or element-store helper would put the layout-write discipline behind one boundary, matching how `string.rs` already delegates string alloc to `heap_string::alloc_string`.

This is the exact `vec_set_copy` RC-asymmetry family the SPRINT.md seed flags as a backend/intrinsics RC-model-alignment candidate — surfaced here from the primitives side as a second witness that Vec element-write discipline is not single-sourced.

**Proposed remediation**: route `str_split`'s element population + len-set and `str_join`'s element read through `vec_runtime` accessors. If `vec_runtime` lacks a suitable public fn, that is an `/arch`-routed addition to the intrinsics Vec surface (cross-reference the `vec_set_copy` seed).

### LOW-1: Stale references to retired `cranelisp-runtime` and `facades/backend.md` in module rustdoc
**Files**: `crates/cranelisp-primitives/src/int.rs:7-14`, `float.rs:5-6`, `bool.rs:5-6`, `ring0.rs:4-5` (and operator.rs:184, 188 — `cranelisp-runtime`)
**Severity**: Low (doc staleness — Principle 8 residue, doc-only) · **routes**: `target: /dev` · **RESOLVED S98 (FIXME 0493)**

Carried forward unresolved from baseline LOW-1. `int.rs`/`float.rs`/`bool.rs` still narrate "Wave 3b-2d.2b lifted the bodies from `cranelisp-runtime/...` … keeps thin re-export shims until that crate retires per FIXME 0150 Phase 5." `cranelisp-runtime` no longer exists (Decision 43 split it into primitives + intrinsics). `ring0.rs:4-5` cites `design/arch/facades/backend.md` §"Non-goals" (retired S75 W5b → BC §3). `operator.rs:184-188` says the string/conversion fns are "implemented as extern C functions in `cranelisp-runtime`" and inlined "in `cranelisp-runtime`" — wrong crate. A newcomer is misdirected to a non-existent crate. **Note**: `marshal.rs:25` already fixed its version of this to a past-tense "lifted from the pre-D43 runtime crate" — that is the model to copy.

**Proposed remediation**: mechanical doc-only sweep replacing `cranelisp-runtime` migration narrative with the past-tense one-liner `marshal.rs:25` uses, and `facades/backend.md` → `bounded-contexts.md` §3.

### LOW-2: `marshal.rs` raw `read_i64`/`write_i64` are offset-indexed free fns, not a typed cell accessor
**Files**: `crates/cranelisp-primitives/src/marshal.rs:130-136` + 19 call sites
**Severity**: Low (risk-surface containment — `/review` §Unsafe code audit) · **routes**: `target: /dev` (Suggestion)

Downgraded from baseline MED-3 (the correctness-coupling concern is closed by HIGH-1's offset single-sourcing). `marshal.rs` remains the crate's `unsafe` concentration (the SList/Sexp marshalling), all reads/writes via the two free fns `read_i64(base, offset)` / `write_i64(base, offset, value)`. Every site carries an adequate `// SAFETY:` note and the unsafe is contained to this one module (findable in one place — satisfies the §Unsafe risk-surface-containment rule). The residual smell is that the raw accessor is a bare `(base, offset)` pair rather than a small typed `AdtCell` wrapper, so a wrong offset is a logic error not a type error. Not actionable beyond a future ergonomic wrapper; recorded for completeness.

**Proposed remediation**: none required this sprint; a future `AdtCell { base }` newtype with `.tag()`/`.field0()`/`.field1()` accessors would make the offsets unmistakable. Suggestion only.

### LOW-3: Three Vec-query GOT slots are never populated, invisible to the test suite
**Files**: `crates/cranelisp-primitives/src/lib.rs:256-262`, `:316-333`
**Severity**: Low (clarity / latent null-deref) · **routes**: `target: /qa` or `target: /dev` (Suggestion)

Carried forward unchanged from baseline LOW-2. `vec-get`/`vec-set`/`vec-push` have no extern body (backend compiles them inline via `vec_codegen`), so their GOT slots stay null by design. This is correct and well-commented, but `every_entry_carries_got_slot` passes (the slot is *allocated*) and `got_slots_hold_extern_ptrs_for_harvested_shims` only checks *harvested* names — so the three null slots are invisible to the suite. A future refactor routing `vec-get` through the GOT-indirect value-position fallback (`(let [g vec-get] …)`) would read a null pointer. This is the one spot BC §4a invariant 5's "the named fn ptr is a legitimate fallback" does not actually hold.

**Proposed remediation**: either (a) a test/comment guard documenting these three are inline-*required* (no fallback), or (b) refine BC §4a invariant 5 to name them as inline-required rather than inline-optional. Suggestion.

### LOW-4: Crate-root rustdoc undercounts the public surface ("nine lines" / "seven pub mod")
**Files**: `crates/cranelisp-primitives/src/lib.rs:88-92`; cross-check `public-api.txt` (10 lines)
**Severity**: Low (doc currency) · **routes**: `target: /dev` (Suggestion)

The crate-root rustdoc asserts the public Rust surface is "**nine lines**: `PRIMITIVES_TABLE` + seven `pub mod` + the crate root" (`lib.rs:91`) and the baseline repeated "nine-line `public-api.txt` baseline." The actual `public-api.txt` is **10 lines**: crate root + 7 `pub mod` (bool/float/int/marshal/ring0/string/vec) + **two** statics (`PRIMITIVES_TABLE` *and* `PRIMITIVES_GOT_SLAB`). The count predates FIXME 0280, which added the `#[export_name] pub static PRIMITIVES_GOT_SLAB`. The narrative omits the second static. (`operator` is correctly `pub(crate)`, so it stays off the surface — that part is right.) Not a surface *drift* (the two statics are both intentional and justified), only a stale count in the prose.

**Proposed remediation**: update the rustdoc count to "ten lines: two `pub static`s (`PRIMITIVES_TABLE` + `PRIMITIVES_GOT_SLAB`) + seven `pub mod` + the crate root."

## Architectural drift summary (as-built vs BC §4a + Decision 0048)

| BC §4a / D0048 commitment | As-built | Verdict |
|---|---|---|
| Single public Rust *item* (table) → "stable across primitive churn" | `public-api.txt` = 10 lines (2 statics + 7 `pub mod` + crate root); stable across primitive churn (no extern is `pub`) | **Met** (count narrative stale — LOW-4) |
| Static `SymbolTable<(),()>` + `Arc<GotTable>`, Arc-cloned at session init | `LazyLock<Arc<SymbolTable<(),()>>>` via `build_primitives_table` | **Met** |
| `into_concrete::<Code,()>` mount | int-side; rustdoc cites exercised cache-restore path | **Met** (no primitives drift) |
| Backend severance (`primitives ⟂ backend`) | backend never named; primitives never names `Code`; GOT-only reach | **Met (structural)** |
| `code: None`; primitive-ness from `kind` | every entry `code: None`, `DefKind::Primitive`; guarded | **Met** |
| Static GOT slab → `--link` symbol (FIXME 0280) | `PRIMITIVES_GOT_SLAB` exported, `with_static_backing`; guarded | **Met** |
| Heap-layout consts from intrinsics/types (inward boundary) | `string`/`vec`/`int`/**`marshal`** all single-sourced now (HIGH-1 fixed) | **Met** (was the baseline's one drift) |
| Consuming convention at extern boundary (invariant 8) | every heap-arg extern consumes; uniform RC inc via `rc::rc_inc` | **Met** |
| Spec-driven evolution; no backend-convenience accretion | inventory matches §A.2/§A.3/§A.4; content harness parity-checks | **Met** |

**Net**: the single substantive baseline drift (HIGH-1 heap-offset duplication) is **closed**. The crate is now in full conformance with its as-designed surface. Residual findings are maintainability polish on the registration seam (MED-1), one cross-crate Vec-layout hand-roll (MED-2), and doc currency (LOW-1/4).

## Agent guidance / apparent traps (refreshed)

- **Adding a primitive is still three coordinated, name-matched edits** (extern body + `#[export_name]`, ring-table row, `extern_shims()` harvest key). A harvest-key typo is a runtime null slot, not a compile error. There is no omission-direction test yet (MED-1).
- **Source heap-layout offsets from `HeapHeader` / intrinsics, never local `const`s.** All four data files now follow this — `marshal.rs:41-53` is the corrected model (derive from `HeapHeader::SIZE`, assert with `const _`).
- **Route RC inc through `cranelisp_intrinsics::rc::rc_inc`.** Both former open-coded sites (`marshal::shallow_rc_inc`, `string::string_identity`) now do — do not reintroduce a bare `*rc_ptr += 1` or `fetch_add`.
- **Don't hand-roll Vec element/len writes** (MED-2) — `str_split`/`str_join` currently do; prefer a `vec_runtime` accessor.
- **`vec-get`/`vec-set`/`vec-push` are inline-only** — their GOT slots are null by design (LOW-3); do not assume a value-position fallback exists.
- **Do not depend on `cranelisp-backend`.** Severance is structural and load-bearing (Principle 18).

## Verification (for whoever actions the backlog)

```bash
cargo nextest run -p cranelisp-primitives
rg -n "cranelisp-runtime|facades/backend.md" crates/cranelisp-primitives/src   # → 0 after LOW-1
rg -n "DATA_PTR_OFFSET|LEN_OFFSET" crates/cranelisp-primitives/src/string.rs    # → routed via vec_runtime after MED-2
# public-api baseline unchanged (10 lines) — all proposed remediation is internal/doc.
```
