//! Cranelisp primitives — user-callable, symbol-table addressable operations.
//!
//! This crate owns the kebab-case operations mounted in the synthetic
//! `primitives` module (for example `add-i64`, `str-concat`, `substring`,
//! `int-to-string`, `quote-sexp`, `vec-len`). Harvest-only ABI bodies such as
//! `sconcat` are registered by their owning synthetic module and have no
//! `PRIMITIVES_TABLE` entry. The sibling `cranelisp-intrinsics` owns
//! allocation, RC and drop mechanics, the typed handle vocabulary and the
//! backend-emitted runtime entry points. The boundary is
//! `design/arch/bounded-contexts.md` §4a; the interior design is
//! `design/primitives/primitives.md`.
//!
//! ## Public Rust API
//!
//! The public Rust surface is the process-static `PRIMITIVES_TABLE`, its
//! exported `PRIMITIVES_GOT_SLAB` backing and the public category modules;
//! `public-api.txt` mechanically enumerates it. Extern wrappers are
//! crate-private `extern "C"` functions carrying
//! `#[unsafe(export_name = "…")]`, so they are linker symbols without being
//! Rust API, and adding, renaming or removing a primitive does not change the
//! baseline. Which primitives exist is governed by the language specification's
//! conformance tests and the one declaration inventory in `declarations.rs`.
//!
//! ## Declaration inventory and table shape
//!
//! Every primitive is one row of the `primitive_declarations!` invocation. A
//! `UserExtern` row installs a settled concrete callable with a
//! `Realization::ExternShim` whose GOT slot holds its generated wrapper. A
//! `UserInline` row installs `Life::Inline`: a callable target the backend
//! lowers directly, with no slot and no wrapper. The whole Vec query family —
//! `vec-get`, `vec-set`, `vec-push` and `vec-len` — is inline. A
//! `HarvestExtern` row generates a harvested wrapper and no table entry. Every
//! entry has `CallableOrigin::RustPrimitive`; no primitive carries compiled
//! code, and the GOT is the only home of an extern primitive's address.
//!
//! ## Link survival
//!
//! There is no `#[used]` anchor (`#[used]` applies only to statics). Extern
//! wrappers survive `--link` dead-code elimination through three mechanisms:
//! the `export_name` attribute emits the linker symbol regardless of Rust
//! visibility; the executable bundle forces `PRIMITIVES_TABLE` at startup; and
//! the table initialiser harvests every wrapper address from the declaration
//! inventory, referencing it from live code.
//!
//! ## Backend severance
//!
//! `cranelisp-primitives` and `cranelisp-backend` do not depend on each other.
//! Primitives builds a `SymbolTable<(), ()>` and never names `Code`; the
//! Binary surface concretises it with `SymbolTable::into_concrete` at session
//! mount and on cache restore, preserving the one shared `Arc<GotTable>`.
//! Extern primitives are then reached through ordinary GOT-indirect calls, and
//! inline primitives are lowered by the backend without crossing a crate edge.

use std::sync::atomic::AtomicPtr;
use std::sync::{Arc, LazyLock};

use cranelisp_types::{GOT_TABLE_SIZE, GotTable, ModuleFullPath, SymbolTable};

pub(crate) mod abi_facts;

/// The writable static slab backing the synthetic `primitives` module's GOT,
/// exported under the canonical link-time symbol `__cranelisp_got_primitives`.
///
/// An extern primitive's fallback/indirect call path emits GOT-indirect
/// dispatch against `__cranelisp_got_primitives` in all modes (`apply.rs`).
/// User/stdlib modules' GOTs are link-time data symbols in object mode
/// (`define_module_got_data`); the primitives GOT must be one too, or `--link`
/// binaries fail at `ld` ("symbol not found: ___cranelisp_got_primitives").
/// A heap allocation can never be a link symbol, so this slab is a process-static array exported under the name and
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
/// Built once on first access. Each session shares this `Arc` and
/// concretises it to its own code parameter at mount, keeping the inner
/// `Arc<GotTable>`, so every session reads the same process-static slots.
///
/// The table holds one callable entry per user-callable row in
/// `declarations.rs`, keyed by the primitive's kebab-case name and carrying
/// its scheme, parameter names, docstring and declared `ModeSummary`.
/// `UserExtern` rows are concrete callables whose GOT slot holds the
/// generated wrapper address; `UserInline` rows (the Vec query family) have
/// no slot or wrapper. `HarvestExtern` rows are not user-callable and create
/// no entry.
pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>> =
    LazyLock::new(|| Arc::new(build_primitives_table()));

/// Build the populated `SymbolTable<(), ()>` returned (wrapped in `Arc`)
/// from the `LazyLock` initialiser.
fn build_primitives_table() -> SymbolTable<(), ()> {
    let mut table = SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from("primitives"));

    // Replace the default heap GOT (from `new_with_params`) with one
    // constructed over the exported static slab `__cranelisp_got_primitives`
    // so the primitives GOT base is a link-time symbol and
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
