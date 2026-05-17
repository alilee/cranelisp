# Facade spec — `crates/cranelisp-primitives/`

**Bounded context citation.** Language-level callable surface — spec-defined operations callable from user code via the `primitives/` module path. Spec-driven evolution; user-addressable. See `bounded-contexts.md` §4a — Primitives.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

`cranelisp-primitives` is one of the two crates produced by Decision 43's split of `cranelisp-runtime`. The other is `cranelisp-intrinsics` (`facades/intrinsics.md`). The split formalises the categorical distinction: primitives are *user-callable* (visible in the symbol table at `primitives/<name>` per `src/CLAUDE.md` "JIT Symbol Names"; addressable as values via GOT slots; backend MAY substitute CLIF inline at direct call sites, but does not reach for trait knowledge to do so); intrinsics are *backend-emitted-call targets* (not in the symbol table; not addressable; ABI tightly coupled to backend's codegen).

---

## Public surface (as-designed)

Per FIXME 0159 resolution — the public Rust surface of `cranelisp-primitives` is **one item**: a static `LazyLock<SymbolTable>` that names the synthetic `primitives` module. The extern fns themselves are `pub(crate)` — they are not part of the published Rust API; their addresses are reachable only via each entry's `got_slot` (a slot in the static table's per-module `GotTable`). `code` is `None` for primitives — primitives have process lifetime, no per-entry lifecycle owner.

```rust
use std::sync::LazyLock;
use cranelisp_types::{ModuleFullPath, SymbolTable};

/// The synthetic `primitives` module's symbol table. Populated at static-init time
/// with one `ModuleEntry::Def { kind: Primitive { kind: Builtin }, got_slot: Some(slot), code: None, … }`
/// entry per primitive named by the spec; the function pointer is written to
/// `PRIMITIVES_TABLE.got().store_slot(slot, fn_ptr)`.
///
/// Per FIXME 0159 resolution — single source of truth for primitives. Both `int`
/// (session init: `tables.insert(ModuleFullPath::primitives(), Arc::new(PRIMITIVES_TABLE.clone()))`)
/// and backend (`register_intrinsics` walks the same static) read from this table.
/// Decoupled from compilation session lifecycle; never invalidates, never rebuilds.
///
/// Type: `SymbolTable` with default `<C = (), L = ()>` — `code` is structurally `None`
/// for primitives because their lifecycle is process-static (the `LazyLock` is the
/// owner; nothing per-entry to drop). The fn ptr is carried in the per-module `GotTable`
/// (the post-rollback **single source of truth** for callable addresses), indexed by
/// `got_slot`. The S66 unification briefly considered a sibling `fn_ptr` field on
/// `ModuleEntry::Def`; that placement was rolled back (`1dc57ae`) as redundant with
/// the GOT — no per-entry pointer field exists. The same GOT-slot pattern covers JIT
/// user fns, linker-loaded user fns, primitives, and platform DLL fns.
///
/// The cycle `cranelisp-primitives → cranelisp-backend` is structurally avoided:
/// `Code` variants do not carry a ptr (they carry the `Arc<Jit>` / `Arc<Linker>`
/// lifecycle owner only — see `facades/backend.md`), so primitives' static can populate
/// the GOT slot without ever naming `Code`. Primitives uses `SymbolTable<C = ()>`
/// (Decision 32 default), which never names `Code` in its type signature; the
/// dependency edge stays `cranelisp-primitives → cranelisp-types` (acyclic).
pub static PRIMITIVES_TABLE: LazyLock<SymbolTable>;
```

The static is built once per process from the in-crate `pub(crate)` extern fns plus per-fn metadata (signature, docstring, kebab-case symbol name); subsequent reads are address-stable for the process lifetime. `int`'s session init installs the static into the per-session `SymbolTables` map at `ModuleFullPath::primitives()`; backend's `register_intrinsics` walks the same static when populating the JITModule's symbol-name lookup table.

The shape requires `ModuleEntry::Def.got_slot: Option<usize>` on each entry (the post-rollback single source of truth for callable addresses) and the per-module `GotTable` API (`store_slot` / `load_slot`) on `SymbolTable`. Both are present in `cranelisp-types`. This is captured in the Wave 0 types-crate authoring plan §1.7-revised (post-rollback).

The substitution table at backend is keyed on `Symbol` (e.g., `add-i64`) only — never on `(TraitName, Symbol, TypeName)` triples — per Decision 43 (no trait knowledge). The named fn ptr remains the addressable backing form for non-substituted call sites; backend MAY substitute inline CLIF at known direct call sites (`add-i64 → iadd`) but is not required to.

### Internal extern fns (`pub(crate)`)

Per FIXME 0159 resolution — these are NOT public. They are referenced only via each `PRIMITIVES_TABLE` entry's GOT slot (`PRIMITIVES_TABLE.got().load_slot(entry.got_slot.unwrap())`). Listed here for facade completeness; the binding contract is the static table, not the Rust source surface.

#### Integer primitives

```rust
pub(crate) extern "C" fn add_i64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn sub_i64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn mul_i64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn div_i64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn mod_i64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn eq_i64(a: i64, b: i64) -> i64;        // returns 0 / 1 in i64
pub(crate) extern "C" fn lt_i64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn gt_i64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn le_i64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn ge_i64(a: i64, b: i64) -> i64;
```

Symbol-table names per `src/CLAUDE.md` JIT-Symbol-Names: `add-i64`, `sub-i64`, `mul-i64`, `div-i64`, `mod-i64`, `eq-i64`, `lt-i64`, `gt-i64`, `le-i64`, `ge-i64`. (Underscore in Rust source; kebab-case at the symbol-table layer.)

Integer comparison rounding-out: `neq-i64` joins the comparison set (`#[export_name = "neq-i64"] pub(crate) extern "C" fn neq_i64(a: i64, b: i64) -> i64`); kebab-case symbol-table name `neq-i64`. Symmetry with `eq-i64`; needed by the resolved trait-method codegen for `Eq` on `Int`.

#### Float primitives

```rust
pub(crate) extern "C" fn add_f64(a: i64, b: i64) -> i64;       // f64 bits ferried through i64 per base-pointer ABI
pub(crate) extern "C" fn sub_f64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn mul_f64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn div_f64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn eq_f64(a: i64, b: i64) -> i64;        // returns 0 / 1 in i64
pub(crate) extern "C" fn neq_f64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn lt_f64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn gt_f64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn le_f64(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn ge_f64(a: i64, b: i64) -> i64;
```

Symbol-table names: `add-f64`, `sub-f64`, `mul-f64`, `div-f64`, `eq-f64`, `neq-f64`, `lt-f64`, `gt-f64`, `le-f64`, `ge-f64`. The `i64`-typed ABI ferries `f64` bit-patterns under the uniform base-pointer ABI (Decision 10); Cranelift codegen reinterprets at the call boundary. Currently no `f64`-typed Rust extern fn signatures appear; the existing `float-to-string` takes `f_bits: i64` for the same reason.

#### Boolean primitives

```rust
pub(crate) extern "C" fn not(b: i64) -> i64;
pub(crate) extern "C" fn eq_bool(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn neq_bool(a: i64, b: i64) -> i64;
```

Symbol-table names: `not`, `eq-bool`, `neq-bool`. `eq-bool` + `neq-bool` mirror the integer/float comparison shape for `Eq` on `Bool`.

#### Primitive type conversions

```rust
pub(crate) extern "C" fn int_to_string(n: i64) -> i64;
pub(crate) extern "C" fn parse_int(s: i64) -> i64;
pub(crate) extern "C" fn float_to_string(f_bits: i64) -> i64;
pub(crate) extern "C" fn bool_to_string(b: i64) -> i64;
// (parse_float and equivalents per the spec's primitive surface)
```

Symbol-table names: `int-to-string`, `parse-int`, `float-to-string`, `bool-to-string`. These return heap-allocated string pointers (allocated through `cranelisp-intrinsics`'s allocator); the consuming-convention rules per Decision 24 apply at the call site.

#### Marshalling primitives

```rust
pub(crate) extern "C" fn sconcat(xs: i64, ys: i64) -> i64;
pub(crate) extern "C" fn quote_sexp(val: i64) -> i64;
```

Symbol-table names: `sconcat`, `quote-sexp`. These are user-callable from `defmacro` clause bodies (the unquote-splice path uses `sconcat`; `quote-sexp` is the marshalling entry point for value-to-sexp embedding). Spec-driven evolution per `spec/09-macros.md`.

#### String + vec primitives (transitional re-exports)

The user-callable string operations (15 fns: `str-concat`, `str-len`, `str-eq`, `str-substring`, `str-char-at`, `str-contains`, `str-starts-with`, `str-ends-with`, `str-to-upper`, `str-to-lower`, `str-trim`, `str-split`, `str-join`, `str-replace`, `string-identity`) plus `vec-len` are part of the user-callable surface this crate publishes and are listed in `PRIMITIVES_TABLE` post-FIXME-0159.

Rust identifier names (per `#[export_name = "…"] pub(crate) extern "C" fn`):

```rust
pub(crate) extern "C" fn str_concat(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn str_len(s: i64) -> i64;
pub(crate) extern "C" fn str_eq(a: i64, b: i64) -> i64;
pub(crate) extern "C" fn str_substring(s: i64, start: i64, end: i64) -> i64;
pub(crate) extern "C" fn str_char_at(s: i64, i: i64) -> i64;
pub(crate) extern "C" fn str_contains(haystack: i64, needle: i64) -> i64;
pub(crate) extern "C" fn str_starts_with(s: i64, prefix: i64) -> i64;
pub(crate) extern "C" fn str_ends_with(s: i64, suffix: i64) -> i64;
pub(crate) extern "C" fn str_to_upper(s: i64) -> i64;
pub(crate) extern "C" fn str_to_lower(s: i64) -> i64;
pub(crate) extern "C" fn str_trim(s: i64) -> i64;
pub(crate) extern "C" fn str_split(s: i64, sep: i64) -> i64;
pub(crate) extern "C" fn str_join(strs: i64, sep: i64) -> i64;
pub(crate) extern "C" fn str_replace(s: i64, from: i64, to: i64) -> i64;
pub(crate) extern "C" fn string_identity(s: i64) -> i64;
pub(crate) extern "C" fn vec_len(v: i64) -> i64;
```

Implementation bodies currently live in `cranelisp-intrinsics` (Wave 3b-2d.2 re-export pattern; FIXME 0180). FIXME 0180 status: **unblocked** post-runtime-retirement (Wave 4a.retire dissolved the Cargo cycle that previously blocked physical relocation). Wave 3 `/dev (primitives)` executes the physical lift: bodies move into `cranelisp-primitives::{string,vec}`, intrinsics drops its versions, the re-export stops. Target-stating: at acceptance, these submodules will physically host the fns under the same `pub(crate)` extern discipline as the ring0 ops; the Rust identifiers + kebab-case symbol-table names are unchanged across the relocation. The current pub-api baseline showing `pub use cranelisp_primitives::str_*` re-exports is **transitional** — post-Wave-3 those become `#[export_name = …] pub(crate)` and disappear from the published Rust API (per FIXME 0159's "one published item" target).

### Module structure

The crate's source is organised into one module per primitive category:

- `cranelisp_primitives::ring0` — arithmetic + comparison ops on `Int`/`Float`/`Bool` (the ring-0 numeric/logical surface).
- `cranelisp_primitives::int` — `int-to-string`, `parse-int`.
- `cranelisp_primitives::float` — `float-to-string`.
- `cranelisp_primitives::bool` — `bool-to-string`.
- `cranelisp_primitives::marshal` — `sconcat`, `quote-sexp` (defmacro-clause marshalling entry points).
- `cranelisp_primitives::string` — string operations (transitional; bodies presently re-exported from `cranelisp-intrinsics` per FIXME 0180; physical relocation in Wave 3).
- `cranelisp_primitives::vec` — `vec-len` (same re-export note).

These submodule names appear in the `cargo-public-api` baseline as `pub mod cranelisp_primitives::{ring0,int,float,bool,marshal,string,vec}` — **internal-but-exposed**. The published Rust API contract is the single `PRIMITIVES_TABLE` static (above). The submodules exist for source organisation; their `pub(crate)` extern-fn members are reachable only via the static table's GOT slots, not via direct `cranelisp_primitives::ring0::add_i64` Rust call paths from consumers. Post-FIXME-0159, individual extern fns are `pub(crate)` so the only thing the submodule namespaces publish are the names themselves (necessary for `#[export_name = "…"]` symbol export at link time).

### `ring0_jit_symbols()` — internal-but-exposed

```rust
pub fn ring0_jit_symbols() -> Vec<(&'static str, *const u8)>;
```

A free function returning `(symbol-name, fn-ptr)` pairs for every ring-0 extern fn (currently consumed by `int`'s JIT-symbols seeding path during session init). **Internal-but-exposed**: pre-FIXME-0159 this is the only way `int` reaches the fn ptrs; post-FIXME-0159 it is **superseded by `PRIMITIVES_TABLE`** — the GOT-slot pattern replaces the (`&'static str`, `*const u8`) tuple stream. Wave 3 `/dev (primitives)` narrows this to `pub(crate)` (or deletes it) as part of the FIXME 0159 implementation; consumers in `int` switch to reading the static table directly. A FIXME is filed (see "Forward-target FIXMEs" below).

### FQTypeName migration verification

Per `facades/types.md` §"FQTypeName migration plan" — primitives has **zero hits at the public surface** for bare `TypeName`. Verification: the publicly-published item set (post-FIXME-0159 target: `PRIMITIVES_TABLE`; pre-FIXME-0159 transitional: the `pub(crate)` extern fns + `ring0_jit_symbols`) names no types — every fn ferries i64/f64 scalars or opaque heap pointers (i64 base-pointer convention per Decision 10). No `TypeName`, no `FQTypeName`, no `TypeExpr`, no `Type` appears in primitives' public-API baseline. FQTypeName migration is a no-op for this crate. (`facades/types.md` line 291 records the same verification on the types-crate side.)

### Forward-target FIXMEs

- FIXME 0159 — `PRIMITIVES_TABLE: LazyLock<SymbolTable>` static, demote extern fns to `pub(crate)`. Target: `/dev (primitives, int)`. Wave 3.
- FIXME 0180 — physical relocation of string + vec bodies from `cranelisp-intrinsics` into `cranelisp-primitives::{string,vec}`. Status: unblocked post-runtime-retirement; pending `/dev (primitives)` execution. Wave 3.
- FIXME 0182 (filed S67 W1) — `ring0_jit_symbols()` superseded by `PRIMITIVES_TABLE`; narrow to `pub(crate)` or delete after `int`'s consumer migrates to the static. Target: `/dev (primitives, int)`. Wave 3.

### Versioning policy (per FIXME 0158 resolution — dissolves into 0159)

Because the public Rust API is one item (`PRIMITIVES_TABLE`), the `cargo-public-api` baseline for `cranelisp-primitives` is **one line** and is stable across primitive churn. Adding, renaming, or deleting a primitive does NOT change the cargo-public-api surface — the extern fns are private; only the static is published, and its type is unchanged.

The **semantic surface** (which primitives exist + their signatures) is governed by **spec conformance tests**, NOT by `cargo-public-api`. Two surfaces, two tools, no overlap:
- Rust public-API drift detection → `cargo-public-api` baseline (one-line, near-static).
- Primitive set + signatures drift detection → spec conformance test suite (`/qa`).

This dissolves the workspace-uniform versioning question raised in FIXME 0158 for this crate's purposes — primitive churn doesn't show up in `cargo-public-api`, so the versioning-on-diff policy is moot here. Other crates with richer Rust public surfaces still need a workspace policy; that is a /arch + /qa question outside this facade's scope.

### Public consts

None.

---

## Types originated here

None. Primitives is a leaf crate publishing extern fns over primitive scalar types (`i64`, `f64`) and opaque heap pointers (`i64` carrying base-pointer convention per Decision 11). No structs, no enums, no DTOs; nothing to mark `#[non_exhaustive]`.

---

## Re-exports

None. Per Principle 15 — facade types live with behaviour; primitives owns no boundary types and re-exports nothing from `cranelisp-types`. Consumers that need `Symbol` / `ModuleFullPath` / `FQTypeName` etc. depend on `cranelisp-types` directly.

---

## Consumed surface

The primitives crate imports from:

- **`cranelisp-types`** — per FIXME 0159 resolution, this is now an acyclic load-bearing dependency. The static `PRIMITIVES_TABLE: LazyLock<SymbolTable>` requires `SymbolTable`, `ModuleEntry`, `DefKind`, `PrimitiveKind`, `Code`, `Symbol`, `Type`, `Scheme`, `ModuleFullPath`, `FQTypeName`, `PrimitiveDef` — the full set needed to construct a populated symbol table at static-init time. The dependency direction `cranelisp-primitives → cranelisp-types` is acyclic; types is the leaf with no workspace dependencies.

That is the entire workspace-crate dependency surface. Primitives does not depend on `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-platform`, `cranelisp-intrinsics`, or `cranelisp` (binary).

In particular: primitives does NOT depend on `cranelisp-intrinsics`. The two crates are siblings under the runtime-split-decision and have independent evolution drivers (spec-driven vs backend-driven). Where a primitive needs to allocate heap (e.g., `int-to-string` returns a heap string), it does so by calling the allocator's extern fn at the linker-resolved name — the same way backend-emitted code calls intrinsics — not by depending on intrinsics as a Rust crate.

---

## Sealed traits

None implemented. Primitives does not implement any trait from `cranelisp-types`.

---

## `#[non_exhaustive]` policy

No public structs or enums; the policy is vacuous.

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-primitives` makes with the rest of the workspace:

1. **User-callable surface.** Every fn here is reachable from user code via the `primitives/<name>` module path. Adding a new primitive is a spec change; deleting or renaming one is a breaking change. Spec-driven evolution.

2. **Symbol-table addressable.** Every primitive has an entry in the synthetic `primitives` module's symbol table, seeded by `int` at session init from `cranelisp-types`'s `primitives()` registry. The entry has a GOT slot; the fn ptr in that slot is what `(let [f +] (f 1 2))` resolves to.

3. **No trait knowledge.** Per Decision 43 — backend's name-keyed substitution table maps `Symbol → cranelift_op` (e.g., `add-i64 → iadd`), never `(TraitName, method, TypeName) → Symbol`. Trait dispatch resolves at typecheck/stdlib level; the resolved target is the impl body, which calls primitives by name; backend substitutes from the resolved name. The `cranelisp_op_*` parallel forms (operator-as-value duplicates) that existed pre-S65 in `cranelisp-runtime/src/primitives/int.rs` are retired by D43's Phase 4 (FIXME 0150) — `add-i64` IS the addressable form via its symbol-table entry.

4. **Inline-substitution is optional.** Backend MAY substitute a primitive call with inline CLIF (e.g., `add-i64 → iadd`) at a known direct call site. It MAY NOT be required to do so — the named fn ptr is a legitimate fallback for indirect calls (operator-as-value, GOT-indirect cross-module calls before linker resolution). Implementation choices about which primitives to inline live in `cranelisp-backend/src/primitives_inline.rs` (post-D43; renamed from `operators.rs`).

5. **Spec-driven evolution.** New primitives appear when the spec requires them (e.g., a new arithmetic op, a new conversion). The crate does not accrete primitives for backend convenience; that is what `cranelisp-intrinsics` is for. The categorical line (user-callable vs backend-emitted-call target) is the load-bearing distinction Decision 43 formalised.

6. **Consuming convention at extern boundary (Decision 24).** Every `#[no_mangle]` extern function MUST consume its heap-typed arguments — dec any heap arg it does not return. Internal Rust helpers may use any local convention; the extern boundary enforces consuming so backend's call sites can emit uniformly. (Identical invariant to intrinsics; same source-of-truth in Decision 24.)

---

## Cross-references

- `bounded-contexts.md` §4a — Primitives BC (full statement)
- `decisions/0043-runtime-split-into-primitives-intrinsics.md` — the split decision
- `facades/intrinsics.md` — sibling crate from the same split
- `facades/types.md` §"Operator / primitive registry" — `PrimitiveDef` + `primitives()` registry consumed for symbol-table seeding
- `facades/backend.md` §"Consumed surface" — backend's name-keyed substitution table consumes primitives by symbol name
- `facades/int.md` §"Consumed surface" — int seeds the synthetic `primitives` module from this crate at session init
- `principles.md` Principle 1 (decoupling — surfaces evolve independently), Principle 7 (no duplicate addressable forms), Principle 15 (facade types live with behaviour)
- `src/CLAUDE.md` "JIT Symbol Names" — the symbol-name convention
