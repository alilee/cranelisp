# Facade spec — `crates/cranelisp-primitives/`

**Bounded context citation.** Language-level callable surface — spec-defined operations callable from user code via the `primitives/` module path. Spec-driven evolution; user-addressable. See `bounded-contexts.md` §4a — Primitives.

This spec is **target-stating** for Sprint 68 close: the binding shape is set by **Decision 0048** — `cranelisp-primitives` owns a statically-constructed `SymbolTable` AND its `Arc<GotTable>`; CompilerSession references the static at startup; from session-init onward primitives dispatch is **functionally equivalent to any other module** (no special case in backend's `symbol_lookup_fn`). Drift detection between as-designed and as-built is the job of `cargo-public-api` (S67 baselines now in force) and `/review`'s per-PR audit, not this document.

`cranelisp-primitives` is one of the two crates produced by Decision 43's split of `cranelisp-runtime`. The other is `cranelisp-intrinsics` (`facades/intrinsics.md`). The split formalises the categorical distinction: primitives are *user-callable* (visible in the symbol table at `primitives/<name>` per `src/CLAUDE.md` "JIT Symbol Names"; addressable as values via GOT slots; backend MAY substitute CLIF inline at known direct call sites, but does not reach for trait knowledge to do so); intrinsics are *backend-emitted-call targets* (not in the symbol table; not addressable; `JITBuilder::symbol(name, ptr)` direct registration is the canonical and only path post-S68 per Decision 0048).

---

## Public surface (as-designed)

Per **Decision 0048** — the public Rust surface of `cranelisp-primitives` is **one item**:

```rust
/// Statically-constructed symbol table + GOT for the synthetic `primitives` module.
/// `Arc<SymbolTable<Code, ()>>` Arc-cloned into every `CompilerSession` at startup.
pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>;
```

The ~22 individual extern fns demote to `pub(crate) extern "C"` with `#[used]` discipline (to prevent DCE in `--link`-mode static archives). `pub fn ring0_jit_symbols()` retires (FIXME 0182 closure). The submodules (`ring0`, `int`, `float`, `bool`, `marshal`, `string`, `vec`) remain `pub mod` for source organisation but their `extern "C"` members are reachable only through `PRIMITIVES_TABLE.got()` slots — never via direct `cranelisp_primitives::ring0::add_i64` Rust call paths from consumers.

### Type shape

`PRIMITIVES_TABLE` is `LazyLock<Arc<SymbolTable<Code, ()>>>` — note the `Arc` wrapper around the `SymbolTable` (the pre-S68 transitional shape was `LazyLock<SymbolTable<(), ()>>` without the `Arc` and with `C = ()`). The `C = Code` parameter is required because the table is now Arc-cloned into the live `SymbolTables<Code, ()>` map carried by `CompilerSession` — type uniformity is load-bearing for the "functionally equivalent to any other module" invariant. The `Arc<GotTable>` reachable via `PRIMITIVES_TABLE.got()` is itself populated at `LazyLock` init and never reallocated for the process lifetime.

```rust
use std::sync::{Arc, LazyLock};
use cranelisp_backend::Code;
use cranelisp_types::{GotTable, ModuleEntry, ModuleFullPath, SymbolTable};

/// The synthetic `primitives` module's symbol table and GOT. Both are constructed
/// once per process at LazyLock init time; the contained `Arc<GotTable>` is
/// populated with raw `*const u8` fn pointers at prescribed slot indices for
/// every non-inlined primitive (ring-0 arithmetic/comparison, marshal, per-type
/// to_string, int/float/bool conversions, string ops, `vec-len`, `not`).
///
/// Per Decision 0048 (A2, revised 2026-05-17 in Phase 3): each
/// `ModuleEntry::Def.code = Some(Code::Primitive)` — the marker variant
/// expressing process-static lifecycle (externally owned by this `LazyLock`).
/// The variant carries no payload. The raw `*const u8` continues to live in
/// the GOT's `AtomicPtr<u8>` per Decision 0035 ("GOT is the single source of
/// truth for callable addresses; no per-entry pointer field") — invariant
/// preserved; the marker variant communicates the lifecycle category at
/// every match site over `code`, never duplicates the address.
///
/// The `Arc` semantics already in `SymbolTable.got: Arc<GotTable>` carry the
/// wiring — primitives' GOT is NOT a new category in Decision 23's two-GOT
/// model; it is the SymbolTable-GOT row of that model, instantiated in static
/// memory rather than in per-session heap. The `Arc<SymbolTable<…>>` outer
/// wrapper is what CompilerSession Arc-clones into `session.symbol_tables`.
pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>;
```

### Static-init contract

At `LazyLock` first-access time, the initialiser performs the following population, atomically observable to all subsequent readers:

1. **SymbolTable population.** One `ModuleEntry::Def` per non-inlined primitive listed in the inventory below (§"Primitives inventory") is inserted under its kebab-case `Symbol` name. Each entry's fields:
   - `scheme` — typecheck `Scheme` from the crate-private `operator::ring{0,1,3}_primitives()` builders. `PrimitiveDef` and the three ring builders are crate-private constructor inputs for this static init (relocated from `cranelisp-types` S69 — H1 stronger disposition; consumers reach the same data via the inserted `ModuleEntry::Def` shape, not via `PrimitiveDef` rows).
   - `kind` — `Box::new(DefKind::Primitive { primitive_kind: PrimitiveKind::Inline, jit_name: Some(JitSymbol::from(name)) })`.
   - `got_slot: Some(N)` — N is allocated deterministically via `SymbolTable::allocate_got_slot()` at init; slot indices are stable for the process lifetime.
   - `code: Some(Code::Primitive)` — per Decision 0048 (A2, revised 2026-05-17): the marker variant expresses process-static lifecycle. No payload; the GOT is the single source of truth for the `*const u8` address (Decision 35 invariant preserved).
   - `visibility: Visibility::Public`, `trait_origin: None`, `ast: None`, `callees: Vec::new()`.

2. **GotTable population.** For each allocated slot N, the corresponding `pub(crate) extern "C" fn`'s address is stored via `table.got.store_slot(N, fn_ptr as *const u8)`. The (symbol → ptr) mapping is built from a single in-crate harvest of every `#[unsafe(export_name = "…")] pub(crate) extern "C" fn` across the submodules; no `Vec<(&str, *const u8)>` is published.

3. **Arc wrap + freeze.** The populated `SymbolTable<Code, ()>` is wrapped in `Arc::new(...)` and returned from the `LazyLock` initialiser. From this point on, the table is treated as read-only by all consumers; the `Arc<GotTable>` inside (via `table.got: Arc<GotTable>`) is similarly read-only for the slots that primitives owns. No further `store_slot` calls land on primitives' GOT after init.

### Session-integration contract

`CompilerSession` startup (per `facades/int.md`) obtains an `Arc::clone` of the static and inserts it into the session's `SymbolTables<Code, ()>` map at `ModuleFullPath::primitives()`:

```rust
// in CompilerSession::new() (or equivalent session init in src/session_v4.rs)
session.symbol_tables.insert(
    ModuleFullPath::primitives(),
    Arc::clone(&*cranelisp_primitives::PRIMITIVES_TABLE),
);
```

The `Arc::clone` is shallow — both the outer `Arc<SymbolTable>` and (transitively) the inner `Arc<GotTable>` are reference-counted shares of the same static-memory backing. There is one and only one `GotTable` for primitives in the process, regardless of how many sessions exist concurrently. Reads from any session resolve through the same atomic-ptr slots.

From session-init onward, primitives dispatch is functionally equivalent to any other module:

- Backend's codegen emits a GOT-indirect load against `__cranelisp_got_primitives` (CLIF: `global_value` on a `Linkage::Import` data symbol — byte-identical to user-to-user cross-module calls per Decision 23).
- The JIT-mode `Module` impl's `symbol_lookup_fn` resolves `__cranelisp_got_primitives` to `symbol_tables[primitives()].got().base_ptr()` — which is the static `GotTable`'s base pointer.
- The emitted code loads the fn ptr from `got_base + slot * 8` and calls.

Backend's `symbol_lookup_fn` carries **no primitives-specific branch**. `JITBuilder::symbol(name, ptr)` direct registration narrows to **intrinsics only** (Decision 43's backend-emitted-call targets that are *not* a module).

### Primitives inventory

The following primitives are populated into `PRIMITIVES_TABLE` at static-init time. Rust identifier on the left, kebab-case symbol-table name (per `#[unsafe(export_name = "…")]`) on the right.

#### Ring-0 arithmetic + comparison (submodule `ring0`)

| Rust ident | Symbol name | Signature |
|---|---|---|
| `add_i64` | `add-i64` | `(i64, i64) -> i64` |
| `sub_i64` | `sub-i64` | `(i64, i64) -> i64` |
| `mul_i64` | `mul-i64` | `(i64, i64) -> i64` |
| `div_i64` | `div-i64` | `(i64, i64) -> i64` |
| `eq_i64` | `eq-i64` | `(i64, i64) -> i64` (0/1) |
| `neq_i64` | `neq-i64` | `(i64, i64) -> i64` (0/1) |
| `lt_i64` | `lt-i64` | `(i64, i64) -> i64` (0/1) |
| `gt_i64` | `gt-i64` | `(i64, i64) -> i64` (0/1) |
| `le_i64` | `le-i64` | `(i64, i64) -> i64` (0/1) |
| `ge_i64` | `ge-i64` | `(i64, i64) -> i64` (0/1) |
| `add_f64` | `add-f64` | `(i64, i64) -> i64` (f64 bits) |
| `sub_f64` | `sub-f64` | `(i64, i64) -> i64` |
| `mul_f64` | `mul-f64` | `(i64, i64) -> i64` |
| `div_f64` | `div-f64` | `(i64, i64) -> i64` |
| `eq_f64` | `eq-f64` | `(i64, i64) -> i64` (0/1) |
| `neq_f64` | `neq-f64` | `(i64, i64) -> i64` (0/1) |
| `lt_f64` | `lt-f64` | `(i64, i64) -> i64` (0/1) |
| `gt_f64` | `gt-f64` | `(i64, i64) -> i64` (0/1) |
| `le_f64` | `le-f64` | `(i64, i64) -> i64` (0/1) |
| `ge_f64` | `ge-f64` | `(i64, i64) -> i64` (0/1) |
| `not` | `not` | `(i64) -> i64` (0/1) — **NEW S68** per Decision 0048 (C1), closes FIXME 0157 |
| `eq_bool` | `eq-bool` | `(i64, i64) -> i64` (0/1) |
| `neq_bool` | `neq-bool` | `(i64, i64) -> i64` (0/1) |

The f64 ops ferry `f64` bit patterns under the uniform base-pointer ABI (Decision 10); Cranelift codegen reinterprets at the call boundary.

Ring-0 inlined ops (`add-i64`, `iadd`-substituted etc.) are unchanged by S68 — backend MAY substitute inline CLIF at known direct call sites per `crates/cranelisp-backend/src/primitives_inline.rs`. The named fn ptr in `PRIMITIVES_TABLE.got()` remains the addressable backing form for indirect uses (operator-as-value, GOT-indirect cross-module calls). Inlined ring-0 ops never touch any symbol table or GOT — they are emitted as raw Cranelift IR.

#### Primitive type conversions (submodules `int`, `float`, `bool`)

| Rust ident | Symbol name | Signature |
|---|---|---|
| `int_to_string` | `int-to-string` | `(i64) -> i64` (heap string ptr) |
| `parse_int` | `parse-int` | `(i64) -> i64` |
| `float_to_string` | `float-to-string` | `(i64) -> i64` |
| `bool_to_string` | `bool-to-string` | `(i64) -> i64` |

Heap-string returns allocate via `cranelisp-intrinsics`'s allocator at the linker-resolved name; consuming-convention per Decision 24 applies at the call site.

#### Marshalling (submodule `marshal`)

| Rust ident | Symbol name | Signature |
|---|---|---|
| `sconcat` | `sconcat` | `(i64, i64) -> i64` |
| `quote_sexp` | `quote-sexp` | `(i64) -> i64` |

User-callable from `defmacro` clause bodies per `spec/09-macros.md`.

#### String operations (submodule `string`)

| Rust ident | Symbol name | Signature |
|---|---|---|
| `str_concat` | `str-concat` | `(i64, i64) -> i64` |
| `str_len` | `str-len` | `(i64) -> i64` |
| `str_eq` | `str-eq` | `(i64, i64) -> i64` (0/1) |
| `str_substring` | `substring` | `(i64, i64, i64) -> i64` |
| `str_char_at` | `char-at` | `(i64, i64) -> i64` |
| `str_contains` | `contains?` | `(i64, i64) -> i64` (0/1) |
| `str_starts_with` | `starts-with?` | `(i64, i64) -> i64` (0/1) |
| `str_ends_with` | `ends-with?` | `(i64, i64) -> i64` (0/1) |
| `str_to_upper` | `to-upper` | `(i64) -> i64` |
| `str_to_lower` | `to-lower` | `(i64) -> i64` |
| `str_trim` | `trim` | `(i64) -> i64` |
| `str_split` | `split` | `(i64, i64) -> i64` |
| `str_join` | `join` | `(i64, i64) -> i64` |
| `str_replace` | `replace` | `(i64, i64, i64) -> i64` |
| `string_identity` | `string-identity` | `(i64) -> i64` |

The three string **query** primitives (`Str → Bool`-ish) carry trailing-`?` Clojure-style predicate names: `contains?`, `starts-with?`, `ends-with?`. The remaining string ops drop the `str-` prefix at the symbol-table layer where the bare form does not collide (`char-at`, `substring`, `to-upper`, `to-lower`, `trim`, `split`, `join`, `replace`); only `str-concat`, `str-len`, `str-eq` retain the prefix.

#### Vec query (submodule `vec`)

| Rust ident | Symbol name | Signature |
|---|---|---|
| `vec_len` | `vec-len` | `(i64) -> i64` |

### Removed from pub surface (S68 narrowing)

The following items were `pub` pre-S68 and become `pub(crate)` (or retire entirely) at S68 close. Cross-reference for the `cargo-public-api` baseline-diff reader:

**Demoted from `pub` to `pub(crate)` with `#[used]` discipline** (22 items):

```
cranelisp_primitives::ring0::add_i64
cranelisp_primitives::ring0::sub_i64
cranelisp_primitives::ring0::mul_i64
cranelisp_primitives::ring0::div_i64
cranelisp_primitives::ring0::add_f64
cranelisp_primitives::ring0::sub_f64
cranelisp_primitives::ring0::mul_f64
cranelisp_primitives::ring0::div_f64
cranelisp_primitives::ring0::eq_i64
cranelisp_primitives::ring0::neq_i64
cranelisp_primitives::ring0::lt_i64
cranelisp_primitives::ring0::gt_i64
cranelisp_primitives::ring0::le_i64
cranelisp_primitives::ring0::ge_i64
cranelisp_primitives::ring0::eq_f64
cranelisp_primitives::ring0::neq_f64
cranelisp_primitives::ring0::lt_f64
cranelisp_primitives::ring0::gt_f64
cranelisp_primitives::ring0::le_f64
cranelisp_primitives::ring0::ge_f64
cranelisp_primitives::ring0::not                       (NEW S68; pub(crate) from authoring)
cranelisp_primitives::ring0::eq_bool
cranelisp_primitives::ring0::neq_bool
cranelisp_primitives::int::int_to_string
cranelisp_primitives::int::parse_int
cranelisp_primitives::float::float_to_string
cranelisp_primitives::bool::bool_to_string
cranelisp_primitives::marshal::sconcat
cranelisp_primitives::marshal::quote_sexp
cranelisp_primitives::string::str_concat
cranelisp_primitives::string::str_len
cranelisp_primitives::string::str_eq
cranelisp_primitives::string::str_substring
cranelisp_primitives::string::str_char_at
cranelisp_primitives::string::str_contains
cranelisp_primitives::string::str_starts_with
cranelisp_primitives::string::str_ends_with
cranelisp_primitives::string::str_to_upper
cranelisp_primitives::string::str_to_lower
cranelisp_primitives::string::str_trim
cranelisp_primitives::string::str_split
cranelisp_primitives::string::str_join
cranelisp_primitives::string::str_replace
cranelisp_primitives::string::string_identity
cranelisp_primitives::vec::vec_len
```

(The exact count is ~45 including `not` because the inventory grew in S67's string-physical-relocation; the binding rule is "every `extern "C"` fn → `pub(crate)`". `#[used]` keeps each linkable into `--link`-mode static archives despite no Rust caller.)

**Retired entirely**:

```
pub fn cranelisp_primitives::ring0::ring0_jit_symbols() -> Vec<(&'static str, *const u8)>
pub use cranelisp_primitives::ring0_jit_symbols          (re-export at crate root)
```

`ring0_jit_symbols()` is superseded by `PRIMITIVES_TABLE` — consumers in `int` and `backend` read symbol entries + GOT slot fn ptrs directly from the static table. Closes FIXME 0182. The cross-cutting consumer migration (backend's `intrinsic_symbols()` primitives entries) is FIXME 0191's body.

**`not` addition.** Authored in S68 per Decision 0048 (C1; resolves FIXME 0157). Spec authority: `spec/appendix-a-builtins.md:79`. Tested by `tests/ring0.rs::boolean_not_true`. Lives in `cranelisp_primitives::ring0` from authoring (`pub(crate) extern "C" fn not(b: i64) -> i64`) — never appears in `pub` form.

### Submodule pub-mod retention

```
pub mod cranelisp_primitives::bool
pub mod cranelisp_primitives::float
pub mod cranelisp_primitives::int
pub mod cranelisp_primitives::marshal
pub mod cranelisp_primitives::ring0
pub mod cranelisp_primitives::string
pub mod cranelisp_primitives::vec
```

These remain `pub mod` for source organisation (and so `#[unsafe(export_name = "…")] pub(crate)` items can carry an `export_name` attribute — the `export_name` mechanism requires the fn be reachable from a `pub` path in the dependency graph for the symbol to land in the staticlib). Their members are `pub(crate)`; no `pub` extern fns reach consumers via Rust paths.

### Versioning policy (Decision 0048 amends FIXME 0158)

Because the public Rust API is one item (`PRIMITIVES_TABLE`), the `cargo-public-api` baseline for `cranelisp-primitives` collapses to a one-line published surface plus the seven `pub mod` lines (internal-but-exposed, retained for `export_name` reachability). The baseline is **stable across primitive churn** — adding, renaming, or deleting a primitive does NOT change the cargo-public-api surface, because the extern fns are `pub(crate)`.

The **semantic surface** (which primitives exist + their signatures) is governed by **spec conformance tests** (`/qa`), NOT by `cargo-public-api`. Two surfaces, two tools, no overlap:
- Rust public-API drift detection → `cargo-public-api` baseline (one-line + seven mod lines, near-static).
- Primitive set + signatures drift detection → spec conformance test suite + the crate-private `operator::ring0_primitives()` builder (constructor input for `PRIMITIVES_TABLE`).

### Public consts

None.

---

## Types originated here

None. Primitives is a leaf crate publishing `extern "C"` fns over primitive scalar types (`i64`, `f64`) and opaque heap pointers (`i64` carrying base-pointer convention per Decision 11). No structs, no enums, no DTOs; nothing to mark `#[non_exhaustive]`.

---

## Re-exports

None. Per Principle 15 — facade types live with behaviour; primitives owns no boundary types and re-exports nothing from `cranelisp-types`. Consumers that need `Symbol` / `ModuleFullPath` / `FQTypeName` etc. depend on `cranelisp-types` directly.

---

## Consumed surface

The primitives crate imports from:

- **`cranelisp-types`** — the bulk of the dependency. The static `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>` requires `SymbolTable`, `ModuleEntry`, `DefKind`, `PrimitiveKind`, `JitSymbol`, `Visibility`, `Symbol`, `Type`, `Scheme`, `ModuleFullPath`, `FQTypeName`. The `PrimitiveDef` row type and `ring{0,1,3}_primitives()` builders live in the crate-private `operator` module (relocated from `cranelisp-types` S69 — H1 stronger disposition; not part of the consumed surface). Acyclic; types is the leaf with no workspace dependencies.

- **`cranelisp-backend`** — for the `Code` type parameter on `SymbolTable<Code, ()>` AND for the `Code::Primitive` marker variant constructed at static-init (per Decision 0048 (A2), revised 2026-05-17). Decision 0041 placed `Code` in `cranelisp-backend`; `cranelisp-primitives` names `Code` and constructs `Code::Primitive` (the variant carries no payload — see Decision 0048 §"Shape"). The dependency edge is `cranelisp-primitives → cranelisp-backend`. **Dep-ban (Decision 0048 §"Structural invariant — backend dep-ban", S68 Phase 3 revision)**: `cranelisp-backend` MUST NOT depend on `cranelisp-primitives` — workspace `[dependencies]` and `[dev-dependencies]` alike. The reverse edge `cranelisp-backend → cranelisp-primitives` is forbidden by the workspace DAG, which structurally enforces the architectural invariant "primitives dispatch reaches code via GOT, never via direct extern". Backend consumes `PRIMITIVES_TABLE` exclusively via the session's `SymbolTables` map (`int` does the Arc-clone insertion at session init); backend has no Rust-path visibility into primitives' fns and therefore physically cannot emit a direct-call instruction targeting a primitive. Acyclic.

Primitives does NOT depend on `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-platform`, `cranelisp-intrinsics`, or `cranelisp` (binary). In particular: primitives does NOT depend on `cranelisp-intrinsics`. Where a primitive allocates heap (e.g., `int-to-string`), it does so by calling the allocator's extern fn at the linker-resolved name — the same way backend-emitted code calls intrinsics — not by depending on intrinsics as a Rust crate.

---

## Sealed traits

None implemented. Primitives does not implement any trait from `cranelisp-types`.

---

## `#[non_exhaustive]` policy

No public structs or enums; the policy is vacuous.

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-primitives` makes with the rest of the workspace:

1. **User-callable surface.** Every fn populated into `PRIMITIVES_TABLE` is reachable from user code via the `primitives/<name>` module path. Adding a new primitive is a spec change; deleting or renaming one is a breaking change. Spec-driven evolution.

2. **Symbol-table addressable.** Every primitive has an entry in the synthetic `primitives` module's symbol table at `ModuleFullPath::primitives()`. Session init Arc-clones the static; entries are visible identically from every concurrent session. The entry's `got_slot: Some(N)` indexes the address — `(let [f +] (f 1 2))` resolves to the fn ptr at that slot.

3. **Uniform dispatch (Decision 0048).** From session-init onward, every primitive call from JIT-emitted code follows the standard cross-module GOT-indirect call sequence. Backend's `symbol_lookup_fn` carries no primitives-specific branch. `JITBuilder::symbol(name, ptr)` direct registration is reserved exclusively for intrinsics. **Structurally enforced** (Decision 0048 §"Structural invariant — backend dep-ban", S68 Phase 3 revision): `cranelisp-backend` does not depend on `cranelisp-primitives`, so backend physically cannot name a primitive's extern fn — the GOT-indirect path is the only path available to it.

4. **No trait knowledge.** Per Decision 43 — backend's name-keyed substitution table maps `Symbol → cranelift_op` (e.g., `add-i64 → iadd`), never `(TraitName, method, TypeName) → Symbol`. Trait dispatch resolves at typecheck level; the resolved target is the impl body, which calls primitives by name; backend substitutes from the resolved name.

5. **Inline-substitution is optional.** Backend MAY substitute a primitive call with inline CLIF (e.g., `add-i64 → iadd`) at a known direct call site. It MAY NOT be required to do so — the named fn ptr in `PRIMITIVES_TABLE.got()` is a legitimate fallback for indirect calls (operator-as-value, GOT-indirect cross-module calls before linker resolution). Implementation choices live in `cranelisp-backend/src/primitives_inline.rs`.

6. **Process-static lifecycle.** `PRIMITIVES_TABLE` and its inner `Arc<GotTable>` are constructed once per process at `LazyLock` first-access; never reallocated; never invalidated. Decision 31's per-batch `JITModule` lifecycle does not apply — primitives are the **named exception** (carve-out stated in Decision 0048; to be reflected in Decision 31's "Consequences" at next amendment). Cache-hit reload (Decision 30) similarly carves primitives out — primitives are never cached (no `.meta.json`, no `.o`); the static is always present at session start.

7. **Spec-driven evolution.** New primitives appear when the spec requires them. The crate does not accrete primitives for backend convenience; that is what `cranelisp-intrinsics` is for. The categorical line (user-callable vs backend-emitted-call target) is the load-bearing distinction Decision 43 formalised and Decision 0048 makes operational.

8. **Consuming convention at extern boundary (Decision 24).** Every `pub(crate) extern "C"` fn MUST consume its heap-typed arguments — dec any heap arg it does not return. Internal Rust helpers may use any local convention; the extern boundary enforces consuming so backend's call sites can emit uniformly.

---

## Cascade pointers

The following facades and design docs depend on this one and must be in sync at S68 close:

- **`facades/backend.md`** — `intrinsic_symbols()` body shrinks (no primitives entries; closes FIXME 0191). The `primitives_inline.rs` retirement narrative updates: GOT-indirect dispatch is *the* path post-S68, inline substitution is the optional optimisation it was always intended to be. **Add dep-ban (S68 Phase 3 revision)**: backend MUST NOT depend on `cranelisp-primitives`; Phase 5 Wave 4 deletes the `cranelisp_primitives::*` Rust paths from `intrinsic_symbols()` and removes the `cranelisp-primitives` line from backend's `Cargo.toml`.
- **`facades/intrinsics.md`** — `JITBuilder::symbol(name, ptr)` narrows to intrinsics-only post-S68. Doc-comment refresh; no public-API change expected.
- **`facades/int.md`** — `CompilerSession` startup references `cranelisp_primitives::PRIMITIVES_TABLE` (Arc-clone insertion into `session.symbol_tables`). No `ring0_jit_symbols()` consumption.
- **exe-bundle / `cranelisp_init_platform`** — `pub use cranelisp_primitives::string;` (and sibling) force-link lines retire; replaced by an explicit `cranelisp_init_primitives()` no-op that forces `LazyLock::force(&PRIMITIVES_TABLE)` at startup (per /arch's Phase 2 recommendation in `sprints/SPRINT.md`). For `--link` mode, the static archive must contain the primitives fns (the `#[used]` discipline on each extern fn) AND the linker-side `.o` data-section GOT for `primitives` is populated at process startup before any compiled code runs.
- **`design/backend/module-caching.md`** (FIXME 0163) — cache-hit reload carve-out for the primitives module (never cached).
- **`design/int/platform-registry-removal.md`** (FIXME 0162) — GOT-as-source-of-truth narrative.
- **`src/CLAUDE.md` §"JIT Symbol Names"** — table row for primitives changes to "GOT-indirect via `PRIMITIVES_TABLE.got()`".
- **`design/arch/fixmes/0161-*.md`** — closes with note "superseded by Decision 0048".

---

## Cross-references

- `bounded-contexts.md` §4a — Primitives BC (full statement)
- `decisions/0048-primitives-static-symboltable-and-got-in-crate.md` — **binding source** for the post-S68 shape
- `decisions/0043-runtime-split-into-primitives-intrinsics.md` — the categorical split
- `decisions/0035-code-enum-integration-layer.md` — GOT as single source of truth (post-rollback canonical statement aligned by 0048)
- `decisions/0031-one-jitmodule-per-compile-batch.md` — the per-batch lifecycle 0048 carves an exception from
- `decisions/0023-uniform-codegen-mode-as-module-property.md` (legacy) — two-GOT model 0048 instantiates for primitives
- `decisions/0030-form-by-form-scheduler-mutual-imports.md` — cache reload path 0048 carves an exception from
- `facades/intrinsics.md` — sibling crate from the runtime split
- `facades/backend.md` §"Consumed surface" — backend's name-keyed substitution table consumes primitives by symbol name
- `facades/int.md` §"Consumed surface" — int Arc-clones the static at session init
- `principles.md` Principle 1 (decoupling), Principle 7 (single source of truth — operative test for static-table-in-crate vs per-batch construction), Principle 8 (no interim implementations — the static-table shape is the target), Principle 15 (facade types live with behaviour)
- `src/CLAUDE.md` "JIT Symbol Names" — the symbol-name convention
- `fixmes/0210-arch-primitives-as-uniform-module-with-symboltable-and-got.md` — primary FIXME this facade refresh resolves
- `fixmes/0157-primitives-not-classification.md` — `not` placement (closed by Decision 0048 (C1))
- `fixmes/0182-dev-primitives-ring0-jit-symbols-narrow-or-delete.md` — `ring0_jit_symbols()` retirement
- `fixmes/0191-*.md` — backend's `intrinsic_symbols()` primitives-entries retirement (sibling cascade)
