# The published Import catalog

Owner: `/design` (intrinsics). The design of `intrinsics_table()` — this crate's
published flat `name → (signature, ptr)` catalog of backend-emitted-call targets
([intrinsics bounded context](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics), invariant 11). Implemented at
`crates/cranelisp-intrinsics/src/catalog.rs`.

## 1. Purpose

The catalog makes the crate self-describing so the single JIT-setup boundary
derives its whole symbol set from one source per owner: GOT data symbols from
`symbol_tables`, and intrinsic Import targets from here. No consumer names a
`cranelisp_intrinsics::*` Rust path to find a target, so the three resolution
points of §4 cannot diverge on the set.

## 2. Shape

`pub fn intrinsics_table() -> &'static [IntrinsicEntry]` — a function returning a
`'static` slice literal, **not** a `pub static`. `IntrinsicEntry` carries a raw
`*const u8`, so a `pub static` of them would require an `unsafe impl Sync`,
while a function handing out a shared `&'static` needs none (recorded in the
`crates/cranelisp-intrinsics/src/catalog.rs` module rustdoc). Consumers iterate; no keyed
lookup is needed at any resolution point, because all of them register every
entry unconditionally.

`IntrinsicEntry` fields:

| Field | Role |
|---|---|
| `name: &'static str` | the emitted-call ABI string — the catalog key and the load-bearing agreement of §4 |
| `ptr: *const u8` | the registered function pointer |
| `param_count: usize` | the `i64` parameter count driving the Cranelift signature loop |
| `has_return: bool` | whether the function returns an `i64` |
| `is_runtime: bool` | classificatory: `runtime/`-prefixed infrastructure vs a user-visible-named target. No dispatch consumer |

**The "signature" half is the `(param_count, has_return)` pair, and must not
become a `cranelisp-types` `Type`.** Invariant 10 forbids `FQTypeName`/`TypeName`
at this surface, and the value-passing C-ABI is uniformly `i64`-in /
`i64`-or-void-out, so arity plus return-ness fully determines the Cranelift
signature. A richer typed signature would add a cross-crate dependency at the
surface for zero codegen gain.

## 3. Contents

The entries are this crate's backend-emitted-call targets, each naming an
in-crate Rust path. **The inventory lives in source, pinned by the closed-set
guard `crates/cranelisp-intrinsics/src/catalog/tests.rs::name_set_is_exactly_the_expected_38`**
— do not keep a second copy here.

Deliberately excluded:

- **The int-owned externs that physically live in `src/`** — currently the
  host-promised `discover-tests`, which must name `Code` and so cannot live
  here. Int registers it directly through `Jit::define_symbol`. This catalog is
  this crate's published contribution, not the whole JIT symbol universe.
- **Primitives**, which are GOT-dispatched through `PRIMITIVES_TABLE` and never
  `JITBuilder::symbol`-registered (invariant 9, Decision 0048).

## 4. Consumer contract

Three resolution points, none of them at codegen:

1. **Backend JIT construct** — `JITBuilder::symbol(e.name, e.ptr)` per entry, and
   `declare_intrinsics_generic` builds each Cranelift `Import` declaration from
   `param_count` + `has_return`.
2. **Int cache-hit load** — `Linker::register_symbol(e.name, e.ptr)` per entry.
3. **`--link`** — no code reads the catalog; the linker resolves the same `name`
   strings against the `cranelisp-intrinsics` archive.

From this crate's side the contract is: the table is iterable, every `name` is
the exact emitted-call ABI string, every `ptr` is a valid function address for
the process lifetime, and `param_count`/`has_return` exactly describe the
extern's `i64` ABI.

## 5. The ABI name agreement

Three independent things must agree on each entry's string: the per-module
extern's `#[export_name]`/`#[no_mangle]` attribute (the archive symbol), the
catalog's `name` (the JIT / cache-hit registration name), and the name the
backend emits its `Import` against (driven by the catalog).

Authoring a catalog row must **not** touch the per-module export attributes or
`pub` paths: the table references the same functions and republishes their
already-established names. A typo in a `name` is an unresolved-symbol failure at
JIT finalize or link time, not a compile error, which is why the closed-set
guard compares literal strings.

## 6. One half of the backend import roster

The compiler's by-name import surface has two halves, and conflating them is the
recurring error:

| Half | What it holds | Home | Closure |
|---|---|---|---|
| **Runtime targets** | this catalog's `name → (arity, ptr)` rows, emitted as `Linkage::Import` | `cranelisp-intrinsics` | **measured**: the §3 closed-set guard fails on a silent addition |
| **Slot-less generic user callables** | `bind`, `race`, `select`, `catch-runtime-error` — host-promised, mounted in the synthetic `primitives` module by `src/bootstrap.rs`, backend-intercepted by name | `src/` | **measured**: `src/bootstrap.rs::bootstrap_generic_uniform_body_roster_is_closed` fails on an added or reclassified member |

Each catalog row also carries **declared representation dependencies**: facts
about the layouts it reads (the uniform `i64` value word, the IO node tag
discipline, the closure drop-glue offset, the `Result` tag order, the Vec header
offsets). Those constants are intrinsics-owned and structurally pinned by
`const _: () = assert!(…)` layout locks, so recording a dependency is a
citation, not a new guard.

**`vec-len` belongs to neither half.** It is an inline primitive declaration
that backend lowers to one length-word load; it has no runtime target and no
by-name import. A `vec-len` row here is a `/review` reject.

## 7. Cross-references

- [intrinsics bounded context](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics), invariants 9, 10 and 11 — Import dispatch,
  the surface's type rules, and the catalog obligation.
- [primitives bounded context](../arch/bounded-contexts.md#4a-primitives-cratescranelisp-primitives),
  invariant 3 and "Rejected shapes" — the precedent this applies to intrinsics.
- [`ownership-and-disposal.md`](ownership-and-disposal.md) §9 — deriving the
  hand-written extern shims from this catalog is a triggered extension.
