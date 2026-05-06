# Facade spec — `crates/cranelisp-primitives/`

**Bounded context citation.** Language-level callable surface — spec-defined operations callable from user code via the `primitives/` module path. Spec-driven evolution; user-addressable. See `bounded-contexts.md` §4a — Primitives.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

`cranelisp-primitives` is one of the two crates produced by Decision 43's split of `cranelisp-runtime`. The other is `cranelisp-intrinsics` (`facades/intrinsics.md`). The split formalises the categorical distinction: primitives are *user-callable* (visible in the symbol table at `primitives/<name>` per `src/CLAUDE.md` "JIT Symbol Names"; addressable as values via GOT slots; backend MAY substitute CLIF inline at direct call sites, but does not reach for trait knowledge to do so); intrinsics are *backend-emitted-call targets* (not in the symbol table; not addressable; ABI tightly coupled to backend's codegen).

---

## Public surface (as-designed)

The primitives crate's public surface is the set of `extern "C"` Rust fns the language exposes by name at `primitives/<name>`. Each has:

- A symbol-table entry seeded by `int`'s prelude-loading path (`PrimitiveDef` from `cranelisp-types`'s `primitives()` registry — see `facades/types.md` §"Operator / primitive registry").
- A GOT slot allocated for it (so `(let [f +] (f 1 2))` reads the address from the slot and indirect-calls it).
- An optional inline-CLIF substitution at backend (when called by name at a known direct call site, backend may emit `iadd` rather than a call); the named fn ptr remains the addressable backing form for non-substituted call sites.

Backend has **no trait knowledge** per Decision 43. The substitution table at backend is keyed on `Symbol` (e.g., `add-i64`) only — never on `(TraitName, Symbol, TypeName)` triples.

### Integer primitives

```rust
#[no_mangle] pub extern "C" fn add_i64(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn sub_i64(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn mul_i64(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn div_i64(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn mod_i64(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn eq_i64(a: i64, b: i64) -> i64;        // returns 0 / 1 in i64
#[no_mangle] pub extern "C" fn lt_i64(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn gt_i64(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn le_i64(a: i64, b: i64) -> i64;
#[no_mangle] pub extern "C" fn ge_i64(a: i64, b: i64) -> i64;
```

Symbol-table names per `src/CLAUDE.md` JIT-Symbol-Names: `add-i64`, `sub-i64`, `mul-i64`, `div-i64`, `mod-i64`, `eq-i64`, `lt-i64`, `gt-i64`, `le-i64`, `ge-i64`. (Underscore in Rust source; kebab-case at the symbol-table layer.)

### Float primitives

```rust
#[no_mangle] pub extern "C" fn add_f64(a: f64, b: f64) -> f64;
#[no_mangle] pub extern "C" fn sub_f64(a: f64, b: f64) -> f64;
#[no_mangle] pub extern "C" fn mul_f64(a: f64, b: f64) -> f64;
#[no_mangle] pub extern "C" fn div_f64(a: f64, b: f64) -> f64;
// (plus comparison ops as the language requires; pre-implementation list will be confirmed at S67+ vertical)
```

### Boolean primitives

```rust
#[no_mangle] pub extern "C" fn not(b: i64) -> i64;
```

### Primitive type conversions

```rust
#[no_mangle] pub extern "C" fn int_to_string(n: i64) -> i64;
#[no_mangle] pub extern "C" fn parse_int(s: i64) -> i64;
#[no_mangle] pub extern "C" fn float_to_string(f: f64) -> i64;
#[no_mangle] pub extern "C" fn bool_to_string(b: i64) -> i64;
// (parse_float and equivalents per the spec's primitive surface)
```

These return heap-allocated string pointers (allocated through `cranelisp-intrinsics`'s allocator); the consuming-convention rules per Decision 24 apply at the call site.

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

- **`cranelisp-types`** — for the `Symbol` and `ModuleFullPath` newtypes consumed by the symbol-table seeding path. (At runtime, the extern fns themselves take only scalar/pointer types and never name `cranelisp-types` items in their signatures; the type-import is for the seeding helper.)

That is the entire dependency surface. Primitives does not depend on `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-platform`, `cranelisp-intrinsics`, or `cranelisp` (binary). It is a leaf in the workspace dependency DAG (paralleling cranelisp-types in that respect, though it does depend on cranelisp-types).

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
