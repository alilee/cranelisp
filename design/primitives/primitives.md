# `cranelisp-primitives` — master design

**Status.** ACTIVE — authored S73 Phase 3 by `/design (cranelisp-primitives)` (2026-05-31). This is the per-crate master design doc (`design/{crate}/{crate}.md`) the `/design` role owns; it supersedes the S66 new-crate slice (`design/primitives/implementation-slice-s66.md`, now historical — the crate exists and the migration it scoped has landed) as the forward-looking design home. Cross-references the binding facade `design/arch/facades/primitives.md` (the as-designed public surface, `/arch`-owned) and the two ratified S73 configuration FIXMEs 0244 / 0245.

**Reads.** `design/arch/facades/primitives.md`; `design/arch/fixmes/{0244,0245}-*.md`; `design/arch/facades/intrinsics.md` §"Heap allocator"/§"Vec runtime layout ABI"; `crates/cranelisp-primitives/src/{lib,operator,string,vec,ring0}.rs`; `crates/cranelisp-types/src/module.rs` (`ModuleEntry::def` builder, `DefKind::Primitive`, `SymbolTable::into_concrete`); `spec/appendix-a-builtins.md` §A.2/§A.3.

---

## 1. Crate shape and bounded context

`cranelisp-primitives` is the **user-callable, symbol-table-addressable** half of Decision 43's runtime split (sibling: `cranelisp-intrinsics`, the backend-emitted-call substrate). Its entire public Rust surface is **one item** — `PRIMITIVES_TABLE` — a statically-constructed symbol table + GOT for the synthetic `primitives` module. Every spec-defined primitive (`add-i64`, `str-concat`, `vec-len`, `not`, …) is reachable from user code via `primitives/<name>`; from session-init onward primitives dispatch is functionally equivalent to any other module (Decision 0048).

The crate imports **exactly two** workspace crates: `cranelisp-types` (the boundary) and `cranelisp-intrinsics` (the runtime substrate — allocator + heap-layout ABI + RC/drop/panic). After S73 it imports **neither `cranelisp-backend` nor anything else**. This is the load-bearing structural fact this sprint lands.

### Quality-attribute stewardship this sprint

| Attribute | This sprint |
|---|---|
| **Simplicity** (Principle 6) | The `Code::Primitive` marker is removed; `code: None` is the builder default. Two hand-rolled 11-field struct literals collapse to three-call builder chains. Layout consts deduplicate to a single source. Net: less code, fewer fields spelled, one fact per place. |
| **Maintainability** | Severing `cranelisp-backend` removes the build-order hostage relationship (primitives no longer waits on backend's cascade to reach green). Blast radius of a backend change no longer reaches primitives' build. |
| **Single source of truth** (Principle 7) | Heap-layout offsets sourced from `cranelisp-intrinsics` exclusively — the three copies (intrinsics + two primitives) collapse to one. Primitive-ness read from `kind: DefKind::Primitive`, not duplicated into `code`. |
| **Decoupling** (Principle 1) / **DAG toward stability** (Principle 3) | `primitives ⟂ backend`. Primitives depends only on the two most-stable downstream crates (types is the leaf; intrinsics is the runtime substrate). |
| **Testability** (Principle 5) | The crate becomes testable in isolation — `cargo nextest run -p cranelisp-primitives` green independent of backend. The new content+behavioural harness exercises the table boundary directly with no session/backend construction. |
| **Concurrency** | Untouched. The `LazyLock<Arc<SymbolTable<(), ()>>>` process-static lifecycle (BC invariant 6) is unchanged in shape; only the type parameter narrows `Code → ()`. No new shared-state dimension. |
| **Performance** | Untouched (Principle 6 — not premature). The static-init cost and GOT-indirect dispatch are unchanged. |

---

## 2. Ordered work-steps for `/dev (primitives)`

These are ordered so the build moves from red (current — primitives does not compile against committed `cranelisp-types`; see §6 risk) toward green with the smallest reversible increments. Steps 1–3 are the source moves; 4 is the harness; 5 is triage; 6 is acceptance.

### Step 1 — Sever `cranelisp-backend` (deliverable A)

**Type narrowing.** Change the published type from `<Code, ()>` to `<(), ()>`:

- `lib.rs:93` — `pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>` (was `<Code, ()>`).
- `lib.rs:98` — `fn build_primitives_table() -> SymbolTable<(), ()>` (was `<Code, ()>`).
- `lib.rs:99` — `SymbolTable::<(), ()>::new_with_params(...)` (was `<Code, ()>`).
- `lib.rs:124`, `lib.rs:161` — `insert_primitive_entry` / `insert_vec_len_entry` `table: &mut SymbolTable<(), ()>` params (was `<Code, ()>`).

**Import removal.**

- Delete `use cranelisp_backend::Code;` (`lib.rs:54`).
- `Cargo.toml` — delete the `cranelisp-backend = { path = "../cranelisp-backend" }` line (`Cargo.toml:15`) and the three-line dep-ban narrative comment above it (`Cargo.toml:9–14`). The `[dependencies]` block reduces to `cranelisp-types`, `cranelisp-intrinsics`, `serde`.

**Preamble rewrite (`lib.rs:1–49` `//!` block).** Two doc sections describe the now-removed coupling and must be rewritten to the severed shape:

- `## Public Rust API — single item` (`lib.rs:13–22`) — change `LazyLock<Arc<SymbolTable<Code, ()>>>` to `LazyLock<Arc<SymbolTable<(), ()>>>`. Add the one-sentence note that `int` concretizes to `<Code, ()>` at the session mount via `into_concrete` (that mount is **S74**, not this sprint — primitives' published type is `<(), ()>` and primitives never names `Code`).
- `## Lifecycle marker — Code::Primitive` (`lib.rs:24–33`) — **delete this section entirely.** Replace with a short `## Lifecycle — code: None` note: each entry carries `code: None` (the `ModuleEntry::def(..).build()` default); primitive-ness is read from `kind: DefKind::Primitive`, never from `code`; the GOT (Decision 35) remains the single source of truth for the `*const u8`.
- `## Backend dep-ban` (`lib.rs:35–41`) — rewrite to the **severed** shape: primitives ⟂ backend (neither names the other). The pre-S73 narrative ("the reverse edge … is permitted and required for the `Code::Primitive` marker") is retired — primitives builds a `<(), ()>` table, constructs no `Code`, and drops `cranelisp-backend` from its manifest. Cite Principle 18 (the dep-ban → bidirectional severance) and Principle 1 (decoupling).
- `lib.rs:71–92` (the `PRIMITIVES_TABLE` rustdoc) — update `LazyLock<Arc<SymbolTable<Code, ()>>>` → `<(), ()>`; strike the closing sentence "Every entry carries `code: Some(Code::Primitive)` per Decision 0048 A2 (revised 2026-05-17): the marker variant expresses process-static lifecycle." Replace with the `code: None` statement (mirrors facade §"Type shape").

The facade §"Type shape" rustdoc block (`facades/primitives.md:30–62`) is the canonical wording target — `/dev` may lift the doc-comment narrative from there verbatim; it is already written to the severed `<(), ()>` shape.

### Step 2 — Builder adoption + `code: None` + drop the retired `DefKind::Primitive` payload (deliverable B)

Replace the two hand-rolled `ModuleEntry::Def { … }` literals with the Tier-1 builder.

**`insert_primitive_entry` (`lib.rs:137–154`).** Replace the `table.insert(prim.name.clone(), ModuleEntry::Def { … })` literal with:

```rust
table.insert(
    prim.name.clone(),
    ModuleEntry::def(scheme, DefKind::Primitive)
        .param_names(prim.param_names.clone())
        .got_slot(slot)
        .build(),
);
```

Builder methods called: `param_names(Vec<Symbol>)`, `got_slot(usize)`, `build()`. **No other setters.** Defaults supply `visibility: Visibility::Public`, `docstring: None`, `trait_origin: None`, `ast: None`, `callees: Vec::new()`, **`seq: 0`** (the field currently missing from the hand-rolled literal — the literal predates the `seq` field; the builder default fixes it), and **`code: None`** (the builder has no `code` setter by design — runtime-state, not constructor-settable; primitives have no reclaimable `Code` resource, so `None` is correct, vindicating the builder invariant rather than working around it).

**`insert_vec_len_entry` (`lib.rs:177–194`).** Same shape:

```rust
table.insert(
    Symbol::from("vec-len"),
    ModuleEntry::def(scheme, DefKind::Primitive)
        .param_names(vec![Symbol::from("v")])
        .got_slot(slot)
        .build(),
);
```

**Critical — `DefKind::Primitive` is payload-free.** The current source constructs `DefKind::Primitive { primitive_kind: PrimitiveKind::Inline, jit_name: Some(JitSymbol::from(...)) }`, but committed `cranelisp-types` (S69 Submission 36) has **retired** both `PrimitiveKind` and the `jit_name` field — `DefKind::Primitive` is now a bare unit variant (`crates/cranelisp-types/src/module.rs:1312`). So this step MUST also:

- Drop `PrimitiveKind` and `JitSymbol` from the `use cranelisp_types::{…}` import (`lib.rs:55–58`) — they are no longer exported.
- Construct bare `DefKind::Primitive` (no struct-fields), at **both** sites.

(This is why the current crate does not compile against committed types — see §6. The builder adoption and the payload drop land together; doing the builder change without the payload drop would leave the crate red.)

The local `scheme` construction (`Scheme { vars, constraints, ty }`) is unchanged in both sites — only the `ModuleEntry::Def { … }` literal is replaced by the builder chain.

### Step 3 — Layout dedup (deliverable E, primitives side)

Single-source the heap-layout offsets from `cranelisp-intrinsics`. The intrinsics-side change (promote `vec_runtime::{LEN_OFFSET, CAP_OFFSET, DATA_PTR_OFFSET}` from `pub(crate)` to `pub`) is a separate Phase-5 `/dev (intrinsics)` step — this crate **consumes** them.

**`vec.rs`.**
- Delete the private `const LEN_OFFSET: usize = 16;` (`vec.rs:20–23`) and its layout-comment block (`vec.rs:8–18` FIXME-0180 narrative re duplication).
- Add `use cranelisp_intrinsics::vec_runtime::LEN_OFFSET;` (the only offset `vec.rs` uses — `vec_len` reads `LEN_OFFSET` at `vec.rs:31`).
- The body `unsafe { *((vec as *const u8).add(LEN_OFFSET) ...) }` is unchanged — it now resolves to the imported const.

**`string.rs`.**
- Delete `const VEC_LEN_OFFSET: usize = 16;` and `const VEC_DATA_PTR_OFFSET: usize = 32;` (`string.rs:66–67`) plus the duplication-narrative comment block above them (`string.rs:57–64`).
- Add `use cranelisp_intrinsics::vec_runtime::{LEN_OFFSET, DATA_PTR_OFFSET};`. Update the two use sites (`split` at `string.rs:186,192`; `join` at `string.rs:210,212`) to reference `LEN_OFFSET` / `DATA_PTR_OFFSET`.
- **Per /arch's soundness note (FIXME 0245): `string.rs` uses only `LEN` + `DATA_PTR` — do NOT import `CAP_OFFSET`.** Importing the unused `CAP_OFFSET` would draw a dead-import warning; the consumed contract for `string.rs` is exactly `{LEN_OFFSET, DATA_PTR_OFFSET}`.
- The `HeapString::{LEN_OFFSET, DATA_OFFSET}` references in `string.rs` (`read_string_parts` at `:37,39`; `str_len` at `:108`) are **already** consuming intrinsics' `pub` consts — no change. `string.rs:23–24` already imports `HeapString, alloc_string`. Do NOT add `HeapString::CAP_OFFSET` (not used; not imported).

After this step `git grep -n "LEN_OFFSET\s*=\|DATA_PTR_OFFSET\s*=\|VEC_LEN_OFFSET\|VEC_DATA_PTR_OFFSET" crates/cranelisp-primitives/src/` returns nothing — zero local layout-const definitions.

### Step 4 — Unit harness (deliverable C)

`/dev`'s unit tests, in `crates/cranelisp-primitives/src/` (unit-tests-with-dev rule). Two table-driven harnesses; the existing `#[cfg(test)] mod tests` in `lib.rs` is the home for (a) and (b) since both read `PRIMITIVES_TABLE`. See §3 for the row schemas.

**(a) Content harness** — one row per primitive asserting the spec contract against the table entry. Schema: `(symbol_name, expected_scheme_ty, expected_param_names, expects_got_slot)`. For each row, look up `PRIMITIVES_TABLE.get(name)`, assert it is a `ModuleEntry::Def`, and assert:
- `scheme.ty == expected_scheme_ty` (the boundary `Type::Fn(...)` per spec §A.3 — note `vec-len`'s boundary scheme is `(Fn [Int] Int)`, the Vec erased to its i64 base-ptr ABI per Decision 11, NOT the user-source `(Fn [(Vec a)] Int)`);
- `param_names == expected_param_names`;
- `got_slot.is_some()`;
- `matches!(*kind, DefKind::Primitive)` (the kind discriminator — see step 5 rewrite of `every_entry_carries_code_primitive_marker`);
- "jit_name" is the symbol-table key itself (S69 Submission 36 — no `jit_name` field; the key IS the JIT linker name). The content row asserts the **key** equals the expected kebab-case name, which the `PRIMITIVES_TABLE.get(name)` lookup already pins.

Rows are sourced from the `operator::ring{0,1,3}_primitives()` builders (already the constructor input) plus the `vec-len` row — so the harness can iterate `ring0_primitives().iter().chain(ring1_primitives()).chain(ring3_primitives())` and assert each `prim`'s `(name, ty, param_names)` round-trips through the inserted entry, then a separate explicit assertion for `vec-len`. This keeps the content harness a *parity* check between the builder input and the table output (it catches insert-path regressions) rather than a hand-maintained second copy of the spec table.

**(b) Behavioural harness** — transmute-and-invoke every **PURE scalar** op against known I/O pairs, extending the existing `not_primitive_present_and_callable` pattern (`lib.rs:374–392`). Schema: `(symbol_name, Invoke, expected)` where `Invoke` is one of the arity/type shapes below. For each row: load the GOT slot ptr, assert non-null, transmute to the matching `extern "C" fn` signature, call with the input(s), assert the result.

Behaviourally testable in this harness (no allocator needed — pure i64/f64-bits-in, i64-out):
- **ring0 Int arithmetic**: `add-i64`, `sub-i64`, `mul-i64`, `div-i64` — `fn(i64,i64)->i64`.
- **ring0 Int comparison**: `eq-i64`, `lt-i64`, `gt-i64`, `le-i64`, `ge-i64` — `fn(i64,i64)->i64` (0/1). (`neq-i64` is in the shim harvest but not a `PRIMITIVES_TABLE` entry — skip; see `extern_shims_harvest_covers_full_inventory`.)
- **ring0 Float arithmetic/comparison**: `add-f64` … `ge-f64` — `fn(i64,i64)->i64` where the i64 args/return are `f64::to_bits` / `f64::from_bits` (the f64-bits ABI per Decision 10). The harness encodes inputs via `f64::to_bits` and decodes via `f64::from_bits` for arithmetic; comparison returns 0/1.
- **ring0 boolean**: `not` (already covered — fold into the table), `eq-bool` — `fn(i64,i64)->i64` (0/1).

**Excluded from this harness** (stay e2e, NOT here): every heap primitive — `int-to-string`, `parse-int`, `float-to-string`, `bool-to-string`, `str-concat`, `str-len`, `str-eq`, `substring`, `char-at`, `contains?`, `starts-with?`, `ends-with?`, `to-upper`, `to-lower`, `trim`, `split`, `join`, `replace`, `string-identity`, `sconcat`, `quote-sexp`, `vec-len`. These need the allocator / a constructed heap value / a HeapString; they are exercised by `string.rs`'s own `#[cfg(test)]` module (which constructs strings via `alloc_string`) and by the e2e suite (`tests/ring1.rs`). `vec-len` reads a heap Vec layout — it stays in `vec.rs`'s existing offset-16 unit test, not the table behavioural harness.

`div-i64` by zero is a **panic-path** primitive (writes a thread-local error, returns 0) — the behavioural row tests only the non-zero happy path (`div_i64(6,2) == 3`); the panic path is e2e (`tests/ring0.rs`), not unit, because asserting the thread-local-error side effect couples to intrinsics' panic slot.

### Step 5 — Triage close (FIXMEs 0182, 0212)

**FIXME 0182 (`ring0_jit_symbols()` retired).** Already gone from source — `git grep -n "fn ring0_jit_symbols" crates/cranelisp-primitives/src/` returns nothing (only a historical comment at `ring0.rs:211`). Check `/dev` runs: `git grep -n "ring0_jit_symbols" crates/cranelisp-primitives/` shows **no fn definition and no call site** (comment-only is acceptable). 0182 is closeable — `/dev` confirms, `/sprint` deletes the FIXME file.

**FIXME 0212 (`#[used]` discipline).** The brief states "confirm present" — but **the `#[used]` attribute is NOT present in source** (verified: the extern fns carry only `#[unsafe(export_name = "…")]`; `#[used]` appears only in two `lib.rs` doc-comment mentions). The facade (`primitives.md` §"Public surface", line 24) and Decision 0048 §"Consequences" prescribe `#[used]`. FIXME 0212 offers two resolutions: (1) `/dev` adds `#[used]` to each `pub(crate) extern "C" fn` (~45 single-line additions, faithful to the current facade), or (2) amend the facade to name `extern_shims()`'s static-data reference as the canonical DCE mechanism. **`/dev` runs Option 1** — add `#[used]` above each `#[unsafe(export_name = "…")]` in `ring0.rs`, `bool.rs`, `int.rs`, `float.rs`, `marshal.rs`, `string.rs`, `vec.rs`. This is faithful to the binding facade and requires no facade edit (facades are `/arch`-owned). Check `/dev` runs after the additions: `git grep -c "#\[used\]" crates/cranelisp-primitives/src/*.rs` equals the count of `#[unsafe(export_name` lines. See §6 — the brief's "confirm present" premise is wrong; I flag it and route to Option 1 rather than file a no-op close.

### Step 6 — Acceptance (restatement for `/dev`)

1. `cargo nextest run -p cranelisp-primitives` is **green, independent of `cranelisp-backend`** (the crate no longer depends on backend; its build/test does not wait on backend's cascade).
2. `crates/cranelisp-primitives/Cargo.toml` `[dependencies]` lists exactly `cranelisp-types`, `cranelisp-intrinsics`, `serde` — **no `cranelisp-backend`**.
3. **No duplicated layout consts** — `git grep` for local `LEN_OFFSET`/`DATA_PTR_OFFSET`/`VEC_*` definitions in `crates/cranelisp-primitives/src/` returns nothing; all offsets sourced from `cranelisp_intrinsics`.
4. `cargo check -p cranelisp-primitives` is warning-free for warnings this change introduces (agents-clean-their-own-crate rule) — in particular no unused-import warning from `PrimitiveKind`/`JitSymbol` (removed) or `CAP_OFFSET` (never imported).
5. `cargo public-api --omit blanket-impls,auto-derived-impls -p cranelisp-primitives > crates/cranelisp-primitives/public-api.txt` regenerated. The published type narrows `SymbolTable<Code, ()>` → `SymbolTable<(), ()>` — a baseline-diff event (`design/arch/CLAUDE.md` §"Baseline-diff discipline"). `/dev` regenerates the baseline in the implementing change-set; `/design`/`/arch` confirm the facade §"Type shape" already names the `<(), ()>` shape (it does); `/review` confirms both in the same diff at PR time.

---

## 3. Harness row schemas (reference)

**Content row** (deliverable C(a)):
```
ContentRow {
    name: &'static str,              // kebab-case symbol-table key
    ty: Type,                        // expected scheme.ty (boundary Type::Fn)
    param_names: &'static [&str],    // expected param_names
}
// asserted: entry is Def; scheme.ty == ty; param_names match; got_slot.is_some();
//           matches!(*kind, DefKind::Primitive); lookup key == name (jit_name == key).
// source: iterate ring0/ring1/ring3_primitives() for parity + explicit vec-len row.
```

**Behavioural row** (deliverable C(b)):
```
enum Invoke {
    I64_I64_I64 { a: i64, b: i64, out: i64 },   // int arith
    I64_I64_Bool { a: i64, b: i64, out: i64 },  // int/bool cmp (0/1)
    F64_F64_F64 { a: f64, b: f64, out: f64 },   // float arith (bits ABI)
    F64_F64_Bool { a: f64, b: f64, out: i64 },  // float cmp (0/1)
    Bool_Bool { a: i64, out: i64 },             // not
}
// per row: slot = entry.got_slot; ptr = PRIMITIVES_TABLE.got.load_slot(slot);
//          assert !ptr.is_null(); transmute to matching extern "C" fn; call; assert out.
// f64 rows: encode a/b via f64::to_bits; decode result via f64::from_bits.
```

**Behaviourally-testable primitive list** (the only rows in C(b)): `add-i64 sub-i64 mul-i64 div-i64 eq-i64 lt-i64 gt-i64 le-i64 ge-i64 add-f64 sub-f64 mul-f64 div-f64 eq-f64 lt-f64 gt-f64 le-f64 ge-f64 not eq-bool` (20 rows). All other primitives are heap/allocator-coupled → e2e / module-local string tests, NOT this harness.

**Rewrite** `every_entry_carries_code_primitive_marker` (`lib.rs:334–352`) → `every_entry_is_def_kind_primitive`: iterate `PRIMITIVES_TABLE.symbols`, assert each is `ModuleEntry::Def` with `matches!(*kind, DefKind::Primitive)`. Drop the `code` assertion entirely (there is no `Code::Primitive` and `code: None` is the universal default — asserting `code.is_none()` is permitted as a belt-and-suspenders but carries no spec contract since `kind` is now authoritative).

---

## 4. What this sprint does NOT do (scope boundary)

- **No `int`-side mount change.** The `into_concrete::<Code, ()>()` session mount (FIXME 0242) is **S74** — `int`-owned. Primitives publishes `<(), ()>`; it does not reach into `int`.
- **No backend-side cleanup.** Deleting the `Code::Primitive` variant from `crates/cranelisp-backend/src/code.rs` and removing the `cranelisp-primitives` line from backend's `Cargo.toml` (the reverse edge) are a **future backend sprint** (FIXME 0244 §sequencing; FIXME 0191). The primitives-side severance lands this sprint; the backend-side is decoupled by the severance.
- **No intrinsics audit.** Only the additive `pub const` exposure of the three `vec_runtime` offsets (a `/dev (intrinsics)` step). The full intrinsics per-crate audit (FIXME 0178, extern-signature review, facade retirement) is a separate future sprint.
- **No facade retirement.** `facades/primitives.md` stays binding (it is the canonical surface this doc cross-references).

---

## 5. Sketch consultation

None. The construction is fully grounded in the facade + FIXMEs 0244/0245 + committed `cranelisp-types` source; no behaviour was ambiguous, no dead-end debugged. Per root `CLAUDE.md` §"Sketch Oracle" the sketch is not a default reference and was not consulted.

---

## 6. Risks and FIXMEs for Phase 5

- **The crate is currently red against committed `cranelisp-types`.** `lib.rs:55–58` imports `PrimitiveKind, JitSymbol` and constructs `DefKind::Primitive { primitive_kind, jit_name }`, but committed types (S69 Submission 36) retired both — `DefKind::Primitive` is a bare unit variant. This is the facade-first migration state (types pushed to target; consumer red until fixed wave-by-wave). **Step 2 fixes it** (drop the payload + imports). `/dev` must NOT treat the existing source as a compiling baseline — the builder adoption and the `DefKind::Primitive`-payload drop are one atomic change.

- **Facade staleness — `DefKind::Primitive` payload.** `facades/primitives.md` §"Static-init contract" item 1 (line 70) and §"Primitives inventory" still describe `kind = DefKind::Primitive { primitive_kind: PrimitiveKind::Inline, jit_name: Some(JitSymbol::from(name)) }`. Committed `cranelisp-types` has retired that payload (bare `DefKind::Primitive`). The facade is `/arch`-owned; I cannot edit it. **FIXME filed: `0246-design-primitives-facade-defkind-primitive-payload-stale.md`, target `/arch`** — requesting the §"Static-init contract"/§"Type shape" rustdoc be updated to bare `DefKind::Primitive` (no `primitive_kind`/`jit_name`), citing S69 Submission 36 + `crates/cranelisp-types/src/module.rs:1312`. Design step 2 already specifies the correct (payload-free) construction so Phase 5 is unblocked regardless.

- **Brief premise wrong — FIXME 0212 `#[used]`.** The Phase-3 brief states the `#[used]` attributes are present ("confirm present"); they are **not** in source (only `export_name`). This doc routes step 5 to FIXME-0212 Option 1 (`/dev` adds them, faithful to the binding facade) rather than a no-op confirmation. No FIXME filed — 0212 is already `target: /design (primitives)` and offers this resolution; the design selects Option 1. `/sprint` should note the brief's premise was incorrect.

- **Dead-import vigilance.** Step 3 must import only the offsets each file uses (`vec.rs`: `LEN_OFFSET`; `string.rs`: `LEN_OFFSET, DATA_PTR_OFFSET`) — importing `CAP_OFFSET` anywhere in primitives draws a dead-code warning (per /arch's soundness note, `string.rs` does not use CAP). The acceptance gate (§2 step 6 item 4) catches this.

---

## 7. Cross-references

- `design/arch/facades/primitives.md` — binding facade (as-designed public surface)
- `design/arch/facades/intrinsics.md` §"Heap allocator"/§"Vec runtime layout ABI" — the consumed layout-ABI contract
- `design/arch/fixmes/0244-*.md` — `code: None`; primitive-ness from `kind` (deliverable B config)
- `design/arch/fixmes/0245-*.md` — heap-layout = intrinsics' blessed public ABI (deliverable E config)
- `design/arch/fixmes/0246-*.md` — (filed this Phase) stale `DefKind::Primitive` payload in facade
- `design/primitives/implementation-slice-s66.md` — historical new-crate slice (superseded by this master)
- `spec/appendix-a-builtins.md` §A.2/§A.3 — the primitive set + signatures (semantic-surface authority)
- `crates/cranelisp-types/src/module.rs` — `ModuleEntry::def` builder; `DefKind::Primitive` (payload-free, `:1312`); `SymbolTable::into_concrete` (`:470`)
- Principles 1 (decoupling), 3 (dep toward stability), 6 (complexity budget), 7 (single source of truth), 18 (primitives ⟂ backend severance)
