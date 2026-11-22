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

**`is_runtime` leaves (S123 packet row K11-b, ACT-0963).** At `4b58ab93`
(read 2026-11-16) source still carries a fourth field,
`is_runtime: bool`, which labels an infrastructure row against a
user-visible-named one. Its only reader is the catalog's own classification
test, and the name prefix already carries the distinction. The removal is
approved and lands in S124 in one change-set:

- the field, and the `runtime:` argument of both row constructors and of every
  row;
- the classification test, the `is_runtime` assertion in the poll-leaf row's
  test, and the field in the compile-fail cells' stand-in `IntrinsicEntry`;
- the field's mentions in the `catalog.rs` and `lib.rs` module documentation.
  The backend's `jit.rs` comment that names it is `dev`(backend)'s.

Expected intrinsics `public-api.txt` effect: −2 (the field at its module path
and at the root re-export). There is no consumer outside the crate, so no other
surface changes.

**The "signature" half is the `(param_count, has_return)` pair, and must not
become a `cranelisp-types` `Type`.** Invariant 10 forbids `FQTypeName`/`TypeName`
at this surface, and the value-passing C-ABI is uniformly `i64`-in /
`i64`-or-void-out, so arity plus return-ness fully determines the Cranelift
signature. A richer typed signature would add a cross-crate dependency at the
surface for zero codegen gain.

### 2.1 The pair is derived from the function's type (ACT-1033)

**Status: built in S123.** It replaced hand-copied pairs, three of which
disagreed with their functions: `runtime/panic`, `runtime/rc_underflow_check`
and `runtime/string_read`.

- **Each row is written once.** It gives the name, the function path and the
  function's `extern "C"` pointer type. A crate-private row constructor casts
  the function to that type and derives both fields from the type. Casting a
  function item to a pointer type with any other signature does not compile.
  So the type cannot disagree with the function, and the pair cannot disagree
  with the type.
- **The derivation is a crate-private trait over `extern "C"` function-pointer
  types**, implemented once per arity up to the largest in the catalog. Two
  rules belong to the trait:
  - **A parameter is admitted only if it is a 64-bit word**: `i64`, `usize`,
    or a raw pointer, on the supported 64-bit targets. A `bool`, `i32` or
    narrower parameter would be declared as `i64` by
    `declare_intrinsics_generic` and misread, so it must not compile.
  - **A return is `i64` (`has_return: true`), or `()` or `!`
    (`has_return: false`).** A narrower return, such as the 32-bit `Poll`,
    must not compile through this trait. The one row that has one is governed
    by §2.2.
- **`IntrinsicEntry`'s public fields are unchanged**, so consumers and
  `public-api.txt` see no delta. Only the construction is private.
- **The table stays a promoted `'static` slice.** The derived fields are
  associated constants of concrete types, and the pointer is the same
  function-to-pointer cast the rows use today.
- **The compile-time agreement replaces the old arity test**, which pinned
  copies rather than functions. A module test pins the corrected rows' derived
  values. After D11 (below) the one remaining is `runtime/panic`, which has no
  return; the pins for `rc_underflow_check` and `string_read` leave with their
  rows.
- **Structural.** The stable toolchain accepts both the promoted associated
  constants and the implementation for a `-> !` pointer type, so
  `runtime_panic`'s divergence is part of its type.
- **Detection proof:** compile-fail cells in the catalog's module tests plant
  mismatched rows for arity, return and narrow-word parameters, and each must
  be refused with the expected error class. A matched control must compile.

### 2.1a Rows without an emitter leave (ACT-1033, row D11)

**Status: in source since `acc3f200`;** row D11 of the retired S124 API packet
(recoverable from Git at `d4e930a7`), approved by the user
on 2026-11-17. Before it, no backend, root or primitives source emitted `runtime/rc_underflow_check` or `runtime/string_read`; JIT
registration and the generic import declaration are their only paths into
codegen. The catalog holds targets of emitted calls (BC §4b invariant 1), so
both rows leave in one change-set:

- **`runtime/rc_underflow_check` is retired:** the public function
  `rc::rc_underflow_check`, its export attribute, its catalog row and its
  module tests. The emitted inline decrement is checked before it runs by
  `runtime/rc_dec_check` under the backend's codegen gate, and the Rust-path
  decrement funnels by the A2 and A3 seam checks
  ([diagnostic modes](diagnostic-modes.md) §5). An emitted post-decrement
  check would be a new backend design, not a use of the row.
- **`runtime/string_read` leaves the catalog, not the crate.** Its catalog row
  and the `#[export_name = "runtime/string_read"]` attribute go;
  `heap_string::string_read` stays a public Rust function with its signature.
  Its one cross-crate consumer is the binary's Rust-path call in
  `src/marshal.rs`, which is unchanged. Its rustdoc states that it is a
  Rust-path operation and no emitted call target.
- **The closed-set guard (§3) loses both names** in the same change-set.
- **No emitted code, cached object or linked executable names either
  symbol**, because nothing ever emitted one. No schema effect. Expected
  intrinsics `public-api.txt` effect: −1, 1 changed (the `string_read` line
  loses its attribute).
- **A future emitter of either operation** adds its row back through the
  inter-crate API gate, with its emitting site and module test
  ([Principle 8](../arch/principles/08-no-interim-implementations.md)).

### 2.2 Address-only rows: the runtime poll leaf (S123 ruling)

`runtime/sleep_pollfn` is not a call target. The backend takes its address
with `func_addr` and stores it as a poll node's `code_ptr`. The trampoline
calls it through `PollFn`, whose return is the 32-bit `repr(i32)` `Poll`. Its
row exists for two reasons. JIT construction and the cache-hit load must
register its pointer under its name (§4). The backend also needs a Cranelift
`Import` declaration to take the address from.

- **The row is built by a second crate-private constructor, the poll-leaf
  row.** It accepts a function only through a cast to
  `cranelisp_platform::PollFn`. This compile-time check is the one that
  matters for this row: the leaf must have exactly the ABI that
  `io.rs::await_poll_node` transmutes its `code_ptr` to. The §2.1 rule
  guarantees an emitted call's ABI. This constructor instead guarantees that
  the leaf matches the trampoline's ABI.
- **Its pair is a fixed constant of that constructor: `(3, true)`.** This is
  the uniform-word declaration that the address is taken from, and its
  consumer is the backend's `sleep` lowering. It does not describe a call
  ABI: the three pointer parameters are 64-bit words, but the `Poll` return
  is not an `i64`. §4's "exactly describes" promise is therefore scoped to
  call-target rows.
- **The general derivation stays strict.** `Poll` is not admitted as a
  return there. Admitting it would make every narrow return type look like a
  callable `i64` return, and an emitted call would read the upper bits of the
  return register, which are undefined.
- **Invariant, asserted with a named falsifier: emitted code never calls a
  poll-leaf row.** The falsifier is an emitted `call` whose callee is the
  `FuncId` of `runtime/sleep_pollfn`, or a CLIF dump of a `sleep` lowering
  that shows one. This is a debt. It becomes structural when the backend takes
  this row's `FuncId` from the catalog declaration as an address-only handle
  and stops making its own matching declaration. That change is
  `design`(backend)'s.
- **Rejected:**
  - *Changing the leaf's signature.* The trampoline's `PollFn` fixes it.
  - *Removing the row.* Then no catalog entry would register the pointer
    for the JIT and the cache-hit load, and a second roster would be needed,
    which Principle 07 forbids.
  - *A public field that marks a row as address-only.* That is a change to
    `IntrinsicEntry`, a public API, for a single row whose misuse already has
    a named falsifier. Principle 06 weighs against it. If a second
    address-only row appears, reopen this as a delta for `arch`.
- **No public-API delta.** The constructor is crate-private, and
  `IntrinsicEntry` and its values are unchanged. `public-api.txt` stays
  +0/−0.

## 3. Contents

The entries are this crate's backend-emitted-call targets, each naming an
in-crate Rust path. **The inventory lives in source, pinned by the closed-set
guard `crates/cranelisp-intrinsics/src/catalog/tests.rs::name_set_is_exactly_the_expected_names`**
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
extern's `i64` ABI, by construction (§2.1). That promise covers
call-target rows. The address-only poll-leaf row is governed by §2.2.

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
| **Slot-less generic user callables** | `bind`, `race`, `select` — host-promised, mounted in the synthetic `primitives` module by `src/bootstrap.rs`, backend-intercepted by name | `src/` | **measured**: `src/bootstrap.rs::bootstrap_generic_uniform_body_roster_is_closed` fails on an added or reclassified member |

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
