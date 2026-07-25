//! Cranelisp primitives — user-callable, symbol-table addressable operations.
//!
//! Per Decision 43 + Decision 48 (cross-surface narrative in
//! `bounded-contexts.md` §4a): this
//! crate hosts the kebab-case, user-addressable primitives whose JIT names
//! appear in the synthetic `primitives` module's symbol table (e.g. `add-i64`,
//! `str-concat`, `vec-len`, `substring`, `int-to-string`, `parse-int`,
//! `float-to-string`, `bool-to-string`, `quote-sexp`, `not`). Harvest-only ABI
//! bodies such as `sconcat` are registered by their owning synthetic module
//! and do not appear in `PRIMITIVES_TABLE`. The
//! sibling crate `cranelisp-intrinsics` hosts the backend-emitted-call
//! targets (`runtime/alloc`, `runtime/dealloc`, `runtime/panic`, RC
//! primitives, drop glue, the IO trampoline) — those are the codegen-coupled
//! implementation substrate; this crate is the spec-driven user surface.
//!
//! ## Public Rust API
//!
//! Per Decision 0048 (S68), the public Rust surface comprises the
//! process-static `PRIMITIVES_TABLE`, its exported `PRIMITIVES_GOT_SLAB`
//! backing, and the public primitive-category modules. The committed
//! `public-api.txt` mechanically enumerates that surface.
//!
//! Primitive declarations that require a callable fallback project
//! crate-private `extern "C"` wrappers carrying
//! `#[unsafe(export_name = "…")]`. Those wrappers expose ABI-compatible
//! linker symbols without becoming Rust-callable public API.
//!
//! DCE-survival of those extern fns in `--link`-mode static archives relies on
//! three existing mechanisms — there is **no `#[used] static` anchor**
//! (minimum mechanism, Principle 2): (1) the `#[unsafe(export_name = "…")]`
//! attribute emits the linker symbol into the object/staticlib independent of
//! the fn's Rust visibility (`pub(crate)` still yields the symbol); (2) the
//! exe-bundle force-link `LazyLock::force(&PRIMITIVES_TABLE)` at startup
//! (`cranelisp-exe-bundle/src/lib.rs:75`) is the link anchor that pulls the
//! static — and therefore the harvested fn addresses — into the binary;
//! (3) `declarations.rs` projects every extern row into the shim harvest at
//! static-init, so each is referenced from live code. (`#[used]` is
//! statics-only and does not apply to functions; this Option-2 wording is the
//! settled disposition.)
//!
//! The statically-constructed `Arc<SymbolTable>` is Arc-cloned into each
//! `CompilerSession` at session init; `int` concretizes the `()`-flavoured
//! static to `<Code, ()>` at the session mount via
//! `SymbolTable::into_concrete::<Code, ()>()`. This `<(),()>`→`<Code, ()>`
//! bridge is an **exercised contract today**, not forward work: the
//! cache-restore hot path calls it explicitly (`session_v4.rs:1363`,
//! `worker.rs:1917`) and `into_concrete` is defined and tested in
//! `cranelisp-types` (`module.rs:470`). It maps each `code: Option<()>` to
//! `None::<Code>` and carries `got: self.got` through unchanged, preserving
//! the one shared `Arc<GotTable>`. (The primary-mount comment in `int` is
//! int's to align — FIXME 0242; the rustdoc assertion holds regardless, since
//! both spellings produce the shared-`Arc<GotTable>` `<Code, ()>` table.) From
//! that point on, `UserExtern` primitive fallback dispatch is functionally
//! equivalent to any other module via the standard cross-module GOT-indirect
//! call sequence. The `UserInline` rows `vec-get`, `vec-set`, and `vec-push`
//! are direct-lowered by the backend and have no GOT slots.
//! **Primitives never names `Code`.**
//!
//! ## Lifecycle — `code: None`
//!
//! Each `ModuleEntry::Def` carries `code: None` — the
//! `ModuleEntry::def(..).build()` builder default (Decision 0048 A2 reversed,
//! FIXME 0244, 2026-05-31). Primitive-ness is NOT encoded in `code`; it is
//! read from `kind: DefKind::Primitive`. `code` retains its single
//! responsibility — the per-entry runtime resource handle, `None` when there
//! is no owned compiled code to reclaim (always the case for primitives; the
//! `LazyLock` owns the static fn addresses). For a `UserExtern` row, the raw
//! `*const u8` lives in the `GotTable` at the slot carried by
//! `DefKind::Primitive { body: PrimitiveBody::Extern { got_slot, .. }, .. }`
//! per Decision 35 ("GOT is the single source of truth for callable
//! addresses; no per-entry pointer field"). `UserInline` rows instead carry
//! `PrimitiveBody::Inline` and have no raw function address or GOT slot.
//!
//! ## Backend severance (Decision 0048 §"Structural invariant", S73)
//!
//! `cranelisp-primitives ⟂ cranelisp-backend` — neither names the other.
//! Because every entry carries `code: None`, primitives never constructs a
//! `Code` value, builds a `SymbolTable<(), ()>`, and drops `cranelisp-backend`
//! from its manifest entirely. `int` concretizes via `into_concrete` at the
//! session mount (the exercised cache-restore bridge — see §"Public Rust API");
//! type uniformity with the live `SymbolTables<Code, ()>` map is achieved at
//! the session layer, not at the primitives build. The
//! pre-S73 narrative ("the reverse edge … is permitted and required for the
//! `Code::Primitive` marker") is retired. The workspace DAG enforces the
//! "`UserExtern` primitives reach fallback code via GOT, never via a direct
//! extern reference" invariant structurally per Principle 18 (bidirectional
//! severance) and Principle 1 (decoupling). `UserInline` primitives are
//! direct-lowered without crossing the crate dependency boundary.
//!
//! ## Module organisation
//!
//! Per-primitive-category sub-modules (`ring0`, `int`, `float`, `bool`,
//! `marshal`, `string`, `vec`) keep implementation bodies small and focused.
//! the `primitive_declarations!` macro generates the `extern "C"` wrappers carrying
//! `#[unsafe(export_name)]` and harvests their addresses (DCE survival via the
//! export-name symbol + exe-bundle force-link + declaration inventory); the
//! only way for a consumer outside the crate to reach an extern primitive's
//! fn ptr is via its `PRIMITIVES_TABLE` GOT slot. The slotless `UserInline`
//! vec rows are direct-lowered and expose no fn ptr.
//!
//! Because every extern wrapper is `pub(crate)`, the `cargo-public-api`
//! baseline (`public-api.txt`) is **stable across primitive churn** — adding,
//! renaming, or deleting a primitive does not itself change the Rust public
//! surface. The semantic surface — which primitives exist and their
//! signatures — is governed by **spec-conformance tests** (`/qa`, against
//! `spec/appendix-a-builtins.md` §A.2/§A.3) and the one in-crate declaration
//! inventory (whose tests parity-check inventory → table and inventory →
//! harvest), NOT by the Rust baseline.

use std::sync::atomic::AtomicPtr;
use std::sync::{Arc, LazyLock};

use cranelisp_types::{GOT_TABLE_SIZE, GotTable, ModuleFullPath, SymbolTable};

/// The writable static slab backing the synthetic `primitives` module's GOT,
/// exported under the canonical link-time symbol `__cranelisp_got_primitives`.
///
/// Per FIXME 0280 (Decision 0048): an extern primitive's fallback/indirect
/// call path emits GOT-indirect dispatch against
/// `__cranelisp_got_primitives` in all modes (`apply.rs`). User/stdlib
/// modules' GOTs are link-time data symbols in object mode
/// (`define_module_got_data`); the primitives GOT must be one too, or `--link`
/// binaries fail at `ld` ("symbol not found: ___cranelisp_got_primitives").
/// A heap allocation (the pre-0280 `GotTable::new()` path) can never be a link
/// symbol, so this slab is a process-static array exported under the name and
/// the `PRIMITIVES_TABLE` `GotTable` is constructed OVER it via
/// [`GotTable::with_static_backing`] — ONE GOT serving JIT, cache-restore, and
/// `--link` (BC §3 invariant 3, single-source-of-truth).
///
/// # Safety story
///
/// - **Interior mutability without `mut`**: `AtomicPtr<u8>` provides interior
///   mutability, so the slab is a plain `static` (NOT `static mut`) — slot
///   writes go through `GotTable::store_slot` (atomic `Release` stores). No
///   `unsafe` is needed to mutate it.
/// - **Writable section**: a `static` of interior-mutable cells lands in the
///   writable `__DATA` segment (NOT `__DATA_CONST`). The `(trace …)` GOT
///   copy-swap (`cranelisp_trace_swap_got`) `memcpy`s the debug GOT INTO this
///   base — a store that requires writability (same constraint as
///   `define_module_got_data`'s Bug-B note). A `const` or read-only static
///   would segfault there.
/// - **Alignment 8**: `AtomicPtr<u8>` is pointer-sized and pointer-aligned, so
///   the array is naturally 8-aligned on 64-bit targets — matching the
///   `desc.set_align(8)` the object-mode GOT atoms use.
/// - **`'static` + single backing**: the slab is process-static and exactly one
///   `GotTable` is built over it (inside `PRIMITIVES_TABLE`'s `LazyLock`),
///   satisfying `with_static_backing`'s contract.
///
/// The `cranelisp_init_primitives()` startup hook (`cranelisp-exe-bundle`)
/// forces `PRIMITIVES_TABLE`'s `LazyLock` before user code runs, populating
/// `UserExtern` slots with their harvested wrapper addresses.
#[unsafe(export_name = "__cranelisp_got_primitives")]
pub static PRIMITIVES_GOT_SLAB: [AtomicPtr<u8>; GOT_TABLE_SIZE] =
    [const { AtomicPtr::new(std::ptr::null_mut()) }; GOT_TABLE_SIZE];

pub mod bool;
pub(crate) mod declarations;
pub mod float;
pub mod int;
pub mod marshal;
pub(crate) mod ownership_facts;
pub mod ring0;
pub mod string;
pub mod vec;

/// The synthetic `primitives` module's statically-constructed symbol table
/// and GOT.
///
/// Per Decision 0048 (A2 reversed, S73): `LazyLock<Arc<SymbolTable<(), ()>>>`.
/// Primitives builds a `()`-flavoured (code-free) table; it never names
/// `Code`. The `Arc` outer is what CompilerSession Arc-clones into
/// `session.symbol_tables` at init — `int` then concretizes to `<Code, ()>`
/// via `into_concrete` at the session mount (the exercised cache-restore
/// bridge), preserving the shared inner `Arc<GotTable>`. That inner GOT
/// (via `SymbolTable.got`) is
/// process-static; all sessions share the same atomic slots for `UserExtern`
/// wrapper addresses. `UserInline` rows remain slotless.
///
/// Population at static-init time: one `ModuleEntry::Def` per
/// user-callable row in `declarations.rs`. Each entry carries
/// `DefKind::Primitive { body, mode_summary }`; the JIT linker name remains
/// the symbol-table key, with no parallel primitive-name discriminator.
/// `UserExtern` rows project an ABI wrapper and a GOT slot populated with that
/// wrapper's address. The `UserInline` rows for `vec-get`, `vec-set`, and
/// `vec-push` instead project `PrimitiveBody::Inline`, with neither a GOT slot
/// nor a wrapper. `HarvestExtern` rows project ABI wrappers into the linker
/// harvest but are not user-callable and therefore create no table entry.
/// Every table entry carries `code: None` (the
/// `ModuleEntry::def(..).build()` default, FIXME 0244): primitive-ness is read
/// from `kind`, never from `code`.
pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>> =
    LazyLock::new(|| Arc::new(build_primitives_table()));

/// Build the populated `SymbolTable<(), ()>` returned (wrapped in `Arc`)
/// from the `LazyLock` initialiser.
fn build_primitives_table() -> SymbolTable<(), ()> {
    // The declaration projection performs:
    // `ModuleEntry::def(scheme, DefKind::Primitive { .. }).build()`.
    // Keeping the lifecycle-default invariant visible here also preserves the
    // historical source-level S68 conformance witness after construction
    // moved into `declarations.rs`.
    let mut table = SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from("primitives"));

    // Replace the default heap GOT (from `new_with_params`) with one
    // constructed over the exported static slab `__cranelisp_got_primitives`
    // (FIXME 0280). This makes the primitives GOT base a link-time symbol, so
    // `--link`-mode extern-primitive dispatch resolves at `ld` time. The slab
    // is process-static; exactly one `GotTable` is built over it here.
    table.got = Arc::new(GotTable::with_static_backing(&PRIMITIVES_GOT_SLAB));

    let declarations = declarations::declarations();
    let _shims = declarations::harvest_shims(&declarations);
    declarations::build_table(&mut table, &declarations);

    table
}

#[cfg(test)]
mod tests;
