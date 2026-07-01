# Primitives Crate Audit

> **Point-in-time assessment (2026-06-14).** Per substance-scoping §1.5, audits are point-in-time opinions, not ongoing ground truth. Current-state sections are authoritative as historical observation at the audit date; `/review` is the continuous-audit role going forward, evaluating implementation against the post-S82 canonical set (BC §4a + Decision 0048 + the crate-root rustdoc). Authored under FIXME `0101` (the deferred runtime/platform audit pass, re-scoped post-D43 to `cranelisp-primitives` + `cranelisp-intrinsics` + `cranelisp-platform`). This is the primitives pass.

**Module**: `crates/cranelisp-primitives/src/` (9 files, 2,854 lines)
**Date**: 2026-06-14
**Scope**: Clarity, simplicity, lack of duplicated code and code-paths, architectural drift (as-built vs BC §4a + Decision 0048), hidden coupling, monolith candidates, test locality
**As-designed reference**: `design/arch/bounded-contexts.md` §4a (the primitives BC + invariants 1–8); Decision 0048 (static `PRIMITIVES_TABLE` + GOT-in-crate + backend severance); the crate-root `//!` rustdoc (`lib.rs:1-96`). No `facades/primitives.md` (retired S74 W3 → BC §4a + source rustdoc).

## Module Overview

`cranelisp-primitives` hosts the language's **user-callable, symbol-table-addressable** operations — the kebab-case primitives (`add-i64`, `str-concat`, `vec-len`, `substring`, `parse-int`, `quote-sexp`, `not`, …) that appear in the synthetic `primitives` module's symbol table and dispatch via GOT-indirect call like any other module. Its sibling `cranelisp-intrinsics` hosts the backend-emitted-call targets (allocator, RC, drop glue, the IO trampoline); the categorical line (user-callable vs backend-emitted) is the load-bearing distinction Decision 43 formalised and Decision 0048 made operational.

The crate is **small and in good architectural health**. The headline design commitments of Decision 0048 are faithfully realised in source:

- **Single public Rust item** — the static `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>`. Every extern fn is `pub(crate)` carrying `#[unsafe(export_name)]`. The `public-api.txt` baseline is nine lines and stable across primitive churn.
- **Backend severance is real and structural** — `cranelisp-primitives ⟂ cranelisp-backend` is confirmed by inspection: backend's `Cargo.toml` does not name primitives; primitives builds `SymbolTable<(), ()>` and never names `Code`. The only consumers of the crate are itself and `cranelisp-exe-bundle`; `int` reaches it transitively and concretizes via `into_concrete`. This severs the inverted-DAG edge cleanly (Principle 18, Principle 1).
- **`code: None` lifecycle** (A2 reversal, FIXME 0244) — primitive-ness is read from `kind: DefKind::Primitive`, not from a `Code` marker; the GOT is the single source of truth for the `*const u8`.
- **Static GOT slab** (FIXME 0280) — the GOT base is the exported `__cranelisp_got_primitives` static, making `--link`-mode dispatch resolve at `ld` time. The `with_static_backing` contract (one `GotTable` over a process-static, interior-mutable `AtomicPtr` slab) is sound and well-documented.

The crate is **not over-engineered, has no god functions, no monoliths, and no stringly-typed stage dispatch.** Tests are numerous and — unlike the backend crate — generally well-localized to their owning modules (the per-category extern bodies carry their own `#[cfg(test)]` blocks; `lib.rs` carries the table-construction and content-harness tests that genuinely belong at the crate root).

### What is working well

- **`lib.rs` is the clean front door** — one builder (`build_primitives_table`), two insert helpers, one extern harvest, no second path. There is no "REPL vs batch" duplication, no parallel registration table (the retired `ring0_jit_symbols()` is gone; the harvest in `extern_shims()` is the single source).
- **The static-init contract is exhaustively documented** in the crate-root `//!` and on `PRIMITIVES_GOT_SLAB` — the DCE-survival "Option-2" reasoning (export-name symbol + exe-bundle force-link + harvest), the writable-`__DATA` segment requirement for the trace GOT copy-swap, and the 8-alignment story are all stated.
- **Single-source-of-truth for heap-layout consts is *mostly* honoured** — `string.rs` and `vec.rs` import `HeapString::{LEN_OFFSET, DATA_OFFSET}` and `vec_runtime::{LEN_OFFSET, DATA_PTR_OFFSET}` from `cranelisp-intrinsics` rather than redeclaring them (per the BC §4a inward boundary / former FIXME 0245). `int.rs` uses `HeapHeader::SIZE`. This is the right pattern — the lapse is isolated (see HIGH-1).
- **Test locality is good** — extern bodies are tested next to their definitions; the crate-root tests are table-shape + content-harness + behavioural-harness coverage that legitimately belongs at the root.

The findings below are therefore mostly MEDIUM/LOW polish, with one HIGH for a single-source-of-truth lapse that directly contradicts the crate's own stated discipline.

## Architecture Illustration

### Current state

```mermaid
sequenceDiagram
    autonumber
    participant Session as int::CompilerSession (startup)
    participant Lazy as PRIMITIVES_TABLE (LazyLock)
    participant Build as build_primitives_table()
    participant Slab as PRIMITIVES_GOT_SLAB (static)
    participant Rings as operator::ring{0,1,3}_primitives()
    participant Harvest as extern_shims()
    participant Externs as ring0/int/float/bool/marshal/string/vec
    participant Intr as cranelisp-intrinsics (alloc/rc/drop/heap_string/vec_runtime/panic)

    Session->>Lazy: Arc-clone into session.symbol_tables
    Session->>Lazy: into_concrete::<Code,()>() (shared Arc<GotTable>)
    Lazy->>Build: first-access init
    Build->>Slab: GotTable::with_static_backing(&PRIMITIVES_GOT_SLAB)
    Build->>Rings: union ring0 + ring1 + ring3 PrimitiveDefs
    Build->>Harvest: (name -> fn ptr) for all #[export_name] externs
    loop each PrimitiveDef + 4 hand-built Vec-query rows
        Build->>Slab: got.store_slot(N, fn_ptr)
        Build->>Build: insert ModuleEntry::def(kind=Primitive, code=None, got_slot=N)
    end
    Note over Externs,Intr: extern bodies call intrinsics for alloc/rc/drop;<br/>marshal.rs hardcodes heap offsets (HIGH-1)
```

### File Metrics

| File | Lines | Responsibility | Tests | unsafe |
|---|---:|---|---:|---:|
| `src/lib.rs` | 850 | Crate facade, `PRIMITIVES_TABLE` static, GOT slab, `build_primitives_table`, two insert helpers, `extern_shims()` harvest, table/content/behavioural/static-backing/docstring harness | 18 | 9 |
| `src/operator.rs` | 517 | `PrimitiveDef` input struct + `ring{0,1,3}_primitives()` constructor data (crate-private) | 10 | 0 |
| `src/string.rs` | 423 | 15 user-callable string extern bodies (`str-concat`…`to-lower`) | 9 | 55 |
| `src/marshal.rs` | 399 | `sconcat` + `quote-sexp` extern bodies; runtime SList/Sexp ADT marshalling | 5 | 21 |
| `src/ring0.rs` | 290 | 23 arithmetic/comparison/boolean extern bodies (i64/f64/bool ABI) | 10 | 23 |
| `src/int.rs` | 203 | `int-to-string`, `parse-int` extern bodies | 9 | 11 |
| `src/float.rs` | 73 | `float-to-string` extern body | 4 | 5 |
| `src/bool.rs` | 52 | `bool-to-string` extern body | 3 | 4 |
| `src/vec.rs` | 47 | `vec-len` extern body | 2 | 2 |

No file exceeds 850 lines; no function approaches the ~100-line `src/CLAUDE.md` ceiling. `sconcat`/`quote_sexp_build` in `marshal.rs` are the densest functions and remain well under the guidance. **No monolith candidates.**

## Findings

### HIGH-1: `marshal.rs` hardcodes heap-layout offset constants that have a single-source-of-truth home — directly contradicting the crate's own stated discipline
**Files**: `crates/cranelisp-primitives/src/marshal.rs:27-33`, `crates/cranelisp-primitives/src/marshal.rs:129` (the literal `+8` rc offset)
**Severity**: High (single source of truth — Principle 7; duplicate heap classification — `sketch/audits/codegen.md` HIGH pattern)

`marshal.rs` declares its own copies of the heap-layout offsets:

```rust
// marshal.rs:27-33
const PAYLOAD_OFFSET: usize = 16;   // == HeapHeader::SIZE
const FIELD0_OFFSET:  usize = 24;   // == HeapHeader::SIZE + 8
const FIELD1_OFFSET:  usize = 32;   // == HeapHeader::SIZE + 16
```

and in `shallow_rc_inc` it open-codes the RC offset as a magic literal:

```rust
// marshal.rs:129
let rc_ptr = (val as *mut u8).add(8) as *mut i64; // rc: i64   <-- == HeapHeader::RC_OFFSET
```

These values all have a canonical, asserted home in `cranelisp-types::heap::HeapHeader`:
- `HeapHeader::SIZE == 16` (the payload offset; `heap.rs:20`)
- `HeapHeader::RC_OFFSET == 8` (statically asserted `== 8` at `heap.rs:30`)

This is precisely the lapse the crate's own siblings avoid: `string.rs` (module rustdoc + `use`) and `vec.rs` import the blessed intrinsics layout-ABI consts and explicitly state "No local copies (single source of truth, Principle 7)"; `int.rs:51-53` correctly uses `HeapHeader::SIZE` and `HeapHeader::SIZE + 8`; `string.rs::string_identity` correctly uses `HeapHeader::RC_OFFSET`. `marshal.rs` alone redeclares them as bare `const`s and a magic `8`. The BC §4a inward boundary (and the former FIXME 0245 it folded) names exactly this contract: primitives consumes the blessed heap-layout-ABI consts from upstream, never local copies.

This is the highest-leverage finding because it is the one place where the heap-layout-duplication HIGH pattern from `sketch/audits/codegen.md` ("heap-vs-stack classification scattered across modules instead of single source") has re-entered the crate. The `FIELD0`/`FIELD1` ADT field offsets (`SIZE+8`, `SIZE+16`) are not currently exposed as named consts anywhere; the right fix derives them from `HeapHeader::SIZE` locally (e.g. `const FIELD0_OFFSET: usize = HeapHeader::SIZE + 8;`) so the payload base stays single-sourced and only the field stride is local.

**Impact**:
- If the heap header layout ever changes (e.g. a generation field, a different RC width), `marshal.rs` silently diverges from every other consumer — the `static_assert(RC_OFFSET == 8)` in `cranelisp-types` would still pass while `marshal.rs`'s `+8` is wrong, producing memory corruption rather than a compile error.
- The crate's own rustdoc claims single-source-of-truth discipline; this is a documented invariant the code violates in one file.

**Proposed remediation** (FIXME `target: /dev`, Severity Important):
1. Replace `PAYLOAD_OFFSET` with `cranelisp_types::HeapHeader::SIZE` (already imported transitively; `int.rs` shows the pattern).
2. Derive `FIELD0_OFFSET`/`FIELD1_OFFSET` from `HeapHeader::SIZE` rather than hardcoding `24`/`32`.
3. Replace the magic `.add(8)` in `shallow_rc_inc` with `HeapHeader::RC_OFFSET`.
4. Update the `marshal.rs` module rustdoc to add the single-source-of-truth note its siblings carry.

### MED-1: RC-manipulation helpers are duplicated across `marshal.rs` and `cranelisp-intrinsics::rc` instead of sourced from the blessed RC API
**Files**: `crates/cranelisp-primitives/src/marshal.rs:125-149` (`shallow_rc_inc`, `deep_rc_inc_slist`), `crates/cranelisp-primitives/src/string.rs:115-127` (`string_identity` open-codes an atomic RC inc)
**Severity**: Medium (duplication; risk-surface for RC bugs)

`string.rs`, `int.rs`, `float.rs`, `bool.rs`, `vec.rs` all reach RC/alloc/drop behaviour through `cranelisp_intrinsics::{alloc, rc, drop}` — the blessed substrate. `marshal.rs` is the outlier: it open-codes its own `shallow_rc_inc` (non-atomic `*rc_ptr += 1`) and `deep_rc_inc_slist`, and `string.rs::string_identity` open-codes an *atomic* (`fetch_add(Release)`) RC inc directly against `HeapHeader::RC_OFFSET`.

Two concerns:
1. **Two RC-inc disciplines coexist** — `marshal.rs`'s is a plain non-atomic increment; `string_identity`'s is an atomic `fetch_add`. The intrinsics `rc` module is the single owner of RC semantics (it already provides `consume_shallow`, `rc_trace`). A primitive RC-inc helper that is *not* sourced from `rc` is exactly the kind of scattered ownership that becomes a correctness divergence under the lenient-eval / spark concurrency that is now live (`ivar_spark` → `rayon::spawn`). The non-atomic increment in `marshal.rs` is a latent data-race hazard if an `sconcat`'d SList is ever shared across a fork-join boundary.
2. **Risk-surface containment** (`/review` §Unsafe code audit) — RC pointer arithmetic should live behind one wrapper, not be re-derived per call site.

**Proposed remediation** (FIXME `target: /dev` with a `/arch` cross-reference if `rc` needs a new entry, Severity Important): route `marshal.rs`'s `shallow_rc_inc` and `string_identity`'s inc through a single `cranelisp_intrinsics::rc` entry point (one of `rc_inc`/`rc_inc_atomic`), eliminating the open-coded pointer arithmetic and unifying the atomicity discipline. If `rc` lacks a suitable public fn, that is a `/arch`-routed addition to the intrinsics RC surface.

### MED-2: The `extern_shims()` harvest is a hand-maintained registry that can silently drift from the extern-fn inventory
**Files**: `crates/cranelisp-primitives/src/lib.rs:342-405`
**Severity**: Medium (single source of truth; maintenance hazard)

`extern_shims()` is a 45-entry hand-written `HashMap<&'static str, *const u8>` mapping each kebab-case name to its fn pointer. It is the single source for GOT population, which is correct — but it is maintained *by hand* in parallel with (a) the `#[unsafe(export_name = "…")]` attributes on the extern fns and (b) the `ring{0,1,3}_primitives()` data tables. A new primitive requires three coordinated edits (extern body + attribute, ring-table row, harvest entry). The string literal in the harvest must exactly match the `export_name` string; a typo yields a null GOT slot at runtime, not a compile error.

The crate *does* guard this seam well: `got_slots_hold_extern_ptrs_for_harvested_shims`, `every_entry_carries_got_slot`, `extern_shims_harvest_covers_full_inventory`, and `static_slab_slots_populated_after_force` together catch most drift. The residual gap is the reverse direction — an extern fn that exists but is *omitted* from the harvest (or whose harvest key is misspelled) would leave a null slot for that name with no test forcing its presence unless it is also a `PRIMITIVES_TABLE` entry. The `neq-i64`/`neq-f64`/`neq-bool`/`sconcat` allow-list in `extern_shims_harvest_covers_full_inventory` is itself a hand-maintained exception set that will accrete.

**Proposed remediation** (FIXME `target: /dev`, Severity Suggestion): consider a single declarative table (or a small macro) that emits the `export_name` attribute, the harvest entry, and feeds the name to the ring builder from one source, so the three edits collapse to one. This is a Suggestion, not Important — the test guards make the current shape safe, just verbose. If left as-is, at minimum add a test that asserts every `#[export_name]` extern is present as a harvest key (closing the omission direction).

### MED-3: `marshal.rs` is the crate's `unsafe` and complexity hot-spot, and its raw-pointer reads/writes are not encapsulated behind a typed accessor
**Files**: `crates/cranelisp-primitives/src/marshal.rs` (21 `unsafe` sites across `read_i64`/`write_i64`/`read_slist`/`quote_sexp_build`/RC helpers)
**Severity**: Medium (risk-surface containment — `/review` §Unsafe code audit)

`marshal.rs` carries 21 `unsafe` occurrences — the SList/Sexp ADT marshalling reads and writes raw i64-tagged heap cells via `read_i64(base, offset)` / `write_i64(base, offset, value)` free functions plus inline `*((base as *const u8).add(offset) …)`. Most carry adequate `// SAFETY:` notes, and the unsafe is contained to this one module (good — the risk surface is findable in one file). The concern is that the raw read/write is offset-indexed against the hardcoded `PAYLOAD/FIELD0/FIELD1` consts (see HIGH-1), so the unsafe correctness depends on offsets that are *not* single-sourced. The two concerns compound: a future heap-layout change touches `cranelisp-types::HeapHeader` and every correctly-sourced consumer, but silently leaves `marshal.rs`'s raw reads pointing at stale offsets.

This is not a Blocker — the `// SAFETY:` discipline is present and the unsafe is module-contained. It is flagged so that the HIGH-1 remediation is understood to also harden the unsafe surface (single-sourcing the offsets makes the raw accesses correct-by-construction against the canonical layout).

**Proposed remediation**: subsumed by HIGH-1 (single-source the offsets) + MED-1 (route RC through intrinsics). No separate FIXME needed beyond cross-referencing this in the HIGH-1 brief.

### LOW-1: Stale cross-references to retired crates/docs in module rustdoc — RESOLVED S98 (FIXME 0493)
**Files**: `crates/cranelisp-primitives/src/ring0.rs:4-5` (`design/arch/facades/backend.md` — retired S75 W5b), `crates/cranelisp-primitives/src/marshal.rs:14-16`, `crates/cranelisp-primitives/src/int.rs:7-14`, `crates/cranelisp-primitives/src/float.rs:5-6`, `crates/cranelisp-primitives/src/bool.rs:5-6` (all cite `cranelisp-runtime` "keeps a thin re-export shim until that crate retires per FIXME 0150 Phase 5" — `cranelisp-runtime` no longer exists post-D43)
**Severity**: Low (doc staleness) · **RESOLVED S98 (FIXME 0493)** — swept per the remediation below.

Several module rustdocs reference artefacts that have since retired:
- `ring0.rs` cites `design/arch/facades/backend.md` §"Non-goals" — that facade retired S75 W5b (→ BC §3 + backend source rustdoc).
- `marshal.rs`, `int.rs`, `float.rs`, `bool.rs` all narrate the "Wave 3b-2d.2b lifted the bodies from `cranelisp-runtime`… keeps a thin re-export shim until that crate retires per FIXME 0150 Phase 5" migration. `cranelisp-runtime` is gone (D43 split into primitives + intrinsics); this is historical narrative pointing at a crate that no longer exists.

These are harmless to a reader who knows the history but mislead a newcomer into looking for `cranelisp-runtime` and `facades/backend.md`.

**Proposed remediation** (FIXME `target: /dev`, Severity Suggestion): a doc-only sweep replacing retired-artefact references with their successors (`facades/backend.md` → BC §3; `cranelisp-runtime` migration narrative → a one-line "lifted from the pre-D43 runtime crate" past-tense note). Mechanical.

### LOW-2: `vec-get`/`vec-set`/`vec-push` carry GOT slots that are intentionally never populated, with the rationale living only in a code comment
**Files**: `crates/cranelisp-primitives/src/lib.rs:247-336` (`insert_vec_query_entries`)
**Severity**: Low (clarity)

Three of the four Vec-query entries (`vec-get`/`vec-set`/`vec-push`) have **no** extern body — they are name-resolution-only entries whose GOT slots stay null because the backend compiles their applications inline (`vec_codegen`). Only `vec-len` has an extern fallback. This is correct and well-commented in `insert_vec_query_entries`, but it is a genuine asymmetry: `every_entry_carries_got_slot` passes (the slot is *allocated*), and `got_slots_hold_extern_ptrs_for_harvested_shims` only checks slots for *harvested* names — so a null slot for `vec-get` is invisible to the test suite. If a future refactor ever routes `vec-get` through the GOT-indirect fallback path (e.g. operator-as-value `(let [g vec-get] …)`), it would read a null pointer.

**Proposed remediation** (FIXME `target: /qa` or `target: /dev`, Severity Suggestion): either (a) add a `// FIXME`-style assertion documenting that these three are inline-only and adding a guard if/when they gain a value-position fallback, or (b) note in BC §4a invariant 5 (inline-substitution is optional) that these three specific primitives are inline-*required* (no fallback exists), which is a stronger statement than the general "MAY substitute" — surfacing the gap at the BC level. This is the one spot where invariant 5's "the named fn ptr is a legitimate fallback" does not actually hold.

## Architectural drift summary (as-built vs BC §4a + Decision 0048)

| BC §4a / D0048 commitment | As-built | Verdict |
|---|---|---|
| Single public Rust item (`PRIMITIVES_TABLE`) | `public-api.txt` = 9 lines (static + 7 `pub mod` + crate root) | **Met** |
| Static `SymbolTable<(),()>` + `Arc<GotTable>`, Arc-cloned at session init | `build_primitives_table()` → `LazyLock<Arc<SymbolTable<(),()>>>` | **Met** |
| `into_concrete::<Code,()>` mount (exercised contract) | Confirmed exercised on cache-restore path (per rustdoc citing `session_v4.rs`, `worker.rs`); int owns the mount | **Met** (int-side; no primitives drift) |
| Backend severance (`primitives ⟂ backend`) | backend `Cargo.toml` does not name primitives; primitives never names `Code`; only consumers = self + exe-bundle | **Met (structural)** |
| `code: None` lifecycle; primitive-ness from `kind` | every entry `code: None`, `DefKind::Primitive`; guarded by `every_entry_is_def_kind_primitive` | **Met** |
| Static GOT slab → `--link` symbol (FIXME 0280) | `PRIMITIVES_GOT_SLAB` exported, `with_static_backing`; guarded by static-backing harness | **Met** |
| Heap-layout consts sourced from intrinsics (inward boundary, FIXME 0245) | `string.rs`/`vec.rs`/`int.rs` ✅; **`marshal.rs` ✗** | **Drift — HIGH-1** |
| Consuming convention at extern boundary (invariant 8) | every extern dec's heap args it does not return; tested | **Met** |
| Spec-driven evolution; no backend-convenience accretion | inventory matches §A.2/§A.3/§A.4; content harness parity-checks | **Met** |

**Net**: the crate is in strong conformance with its as-designed surface. The single substantive drift is the `marshal.rs` heap-offset duplication (HIGH-1), which contradicts the crate's own stated single-source-of-truth discipline. Everything else is doc staleness and maintainability polish.

## Agent Guidance / Apparent Traps

- **Source heap-layout offsets from `cranelisp-types::HeapHeader` and `cranelisp-intrinsics`, never local `const`s.** `string.rs`/`vec.rs`/`int.rs` are the model; `marshal.rs` is the anti-pattern (HIGH-1). Do not copy `marshal.rs`'s `PAYLOAD_OFFSET`/`FIELD0_OFFSET` pattern into a new primitive.
- **Route RC inc/dec through `cranelisp_intrinsics::rc`, never open-code `*rc_ptr += 1` or a bare `fetch_add`.** Two disciplines already coexist (MED-1); do not add a third.
- **Adding a primitive is three coordinated edits** (extern body + `#[export_name]`, ring-table row, `extern_shims()` harvest key) — the names must match exactly. The test suite catches most drift; the omission direction (extern present, harvest key missing/misspelled) is the residual gap (MED-2).
- **Do not depend on `cranelisp-backend` from this crate.** The severance is structural and load-bearing (Principle 18). Backend reaches primitives only via the GOT.
- **`vec-get`/`vec-set`/`vec-push` are inline-only** — their GOT slots are null by design. Do not assume a value-position fallback exists (LOW-2).

## Proposed FIXMEs for /sprint to file (Wave-3 step)

This audit does **not** file remediation FIXMEs (that is `/sprint`'s Wave-3 step). The candidates, in priority order:

1. **(Important, `target: /dev`) — HIGH-1**: single-source the heap-layout offsets in `marshal.rs` from `HeapHeader::{SIZE, RC_OFFSET}`; derive `FIELD0/FIELD1` from `SIZE`; add the single-source-of-truth rustdoc note. `refers_to: crates/cranelisp-primitives/src/marshal.rs:27-33,129; crates/cranelisp-types/src/heap.rs; bounded-contexts.md §4a`.
2. **(Important, `target: /dev`, `/arch` cross-ref) — MED-1**: route `marshal.rs::shallow_rc_inc` + `string.rs::string_identity` RC inc through a single `cranelisp_intrinsics::rc` entry point; unify atomicity. If `rc` lacks a suitable public fn, `/arch` extends the intrinsics RC surface.
3. **(Suggestion, `target: /dev`) — MED-2**: collapse the three-edit primitive-registration seam (or add an "every `#[export_name]` extern is a harvest key" test closing the omission direction).
4. **(Suggestion, `target: /dev`) — LOW-1**: doc-only sweep of stale `cranelisp-runtime` / `facades/backend.md` references in module rustdocs.
5. **(Suggestion, `target: /qa` or `/dev`) — LOW-2**: surface the inline-only `vec-get`/`vec-set`/`vec-push` null-slot gap (BC §4a invariant 5 refinement, or a guard).

## Verification

After implementing the remediation plan:

```bash
cargo check -p cranelisp-primitives
cargo nextest run -p cranelisp-primitives
rg -n "const (PAYLOAD|FIELD0|FIELD1)_OFFSET" crates/cranelisp-primitives/src     # should resolve to HeapHeader-derived
rg -n "\.add\(8\)" crates/cranelisp-primitives/src/marshal.rs                      # should be HeapHeader::RC_OFFSET
rg -n "cranelisp-runtime|facades/backend.md" crates/cranelisp-primitives/src      # should be 0 after LOW-1
```

Success signals:
- no bare heap-offset `const` declarations remain in `marshal.rs`; offsets derive from `HeapHeader`,
- RC manipulation routes through `cranelisp_intrinsics::rc`,
- stale crate/facade references are gone,
- the nine-line `public-api.txt` baseline is unchanged (all remediation is internal — no public-surface churn).
