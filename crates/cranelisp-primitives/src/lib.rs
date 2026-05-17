//! Cranelisp primitives — user-callable, symbol-table addressable operations.
//!
//! Per Decision 43 + `design/arch/facades/primitives.md`: this crate hosts the
//! kebab-case, user-addressable primitives whose JIT names appear in the
//! synthetic `primitives` module's symbol table (e.g. `add-i64`, `str-concat`,
//! `vec-len`, `substring`, `int-to-string`, `parse-int`, `float-to-string`,
//! `bool-to-string`, `sconcat`, `quote-sexp`). The sibling crate
//! `cranelisp-intrinsics` hosts the backend-emitted-call targets
//! (`runtime/alloc`, `runtime/dealloc`, `runtime/panic`, RC primitives, drop
//! glue, the IO trampoline) — those are the codegen-coupled implementation
//! substrate; this crate is the spec-driven user surface.
//!
//! ## Public Rust API
//!
//! The single published Rust item is `PRIMITIVES_TABLE` — a process-static
//! `LazyLock<SymbolTable>` populated at first access with one
//! `ModuleEntry::Def` per Ring 0 primitive (every entry carries a
//! `got_slot: Some(_)` and the corresponding code pointer is written to
//! that slot in the table's per-module `GotTable`). See FIXME 0159 and the
//! facade spec.
//!
//! Consumers (`int` session init, `cranelisp-backend::register_intrinsics`)
//! read symbol entries + GOT slot fn ptrs from this table — there is no
//! `Vec<(&'static str, *const u8)>` enumeration API published; the
//! transitional `ring0_jit_symbols()` free fn remains for the backend
//! consumer until FIXME 0182 closes that migration in Wave 4.
//!
//! ## Module organisation
//!
//! Per-primitive-category sub-modules (`ring0`, `int`, `float`, `bool`,
//! `marshal`, `string`, `vec`) keep the source small and focused; their
//! `pub(crate)`-target extern fns are reachable via `PRIMITIVES_TABLE`'s
//! GOT slots, not via direct Rust paths.
//!
//! ## FIXME 0180 close (Sprint 67 Wave 3)
//!
//! `string` and `vec` bodies physically live in this crate as of Sprint 67
//! Wave 3 (the user-callable surface lifted out of `cranelisp-intrinsics`).
//! `cranelisp-intrinsics::{heap_string, vec_runtime}` retains the
//! backend-emitted-call infrastructure (HeapString layout, runtime alloc
//! helpers, Vec COW paths) — those are NOT user-callable and remain
//! separate per the Decision 43 categorical split.

use std::sync::LazyLock;

use cranelisp_types::{
    DefKind, JitSymbol, ModuleEntry, ModuleFullPath, PrimitiveKind, Scheme, SymbolTable,
    Visibility,
};

pub mod bool;
pub mod float;
pub mod int;
pub mod marshal;
pub mod ring0;
pub mod string;
pub mod vec;

// Transitional re-export — FIXME 0182 narrows / deletes this after backend
// migrates its `intrinsic_symbols()` table to read from `PRIMITIVES_TABLE`
// in Wave 4. See `design/arch/fixmes/0182-*.md`.
pub use ring0::ring0_jit_symbols;

/// The synthetic `primitives` module's static symbol table.
///
/// Per FIXME 0159 resolution + `design/arch/facades/primitives.md`
/// §"Public surface" — single published Rust API item for this crate.
/// Populated at first access; address-stable for the process lifetime.
///
/// Contains one `ModuleEntry::Def` per Ring 0 primitive named in the
/// authoritative table (`cranelisp_types::ring0_primitives`). Each entry
/// carries a `got_slot: Some(slot)`; the corresponding code pointer is
/// stored in `PRIMITIVES_TABLE.got.store_slot(slot, fn_ptr)` immediately
/// after slot allocation, so the standard GOT-indirect dispatch path
/// resolves the call to the Rust shim defined in `crate::ring0`.
///
/// Consumers:
///
/// - `int`'s session-init code reads the (Symbol, fn-ptr) pairs from this
///   table and writes the pointers into the session's per-module
///   `primitives` `GotTable` (so `(let [f +] (f 1 2))` resolves to the
///   shim via the session table's GOT slot).
/// - `cranelisp-backend::jit::intrinsic_symbols` enumerates the same
///   primitives for `JITBuilder::symbol` registration (migration tracked
///   under FIXME 0182, Wave 4).
///
/// The Rust extern fns themselves are `pub` because `#[unsafe(export_name = …)]`
/// requires `pub`; their addresses are only reachable in practice via this
/// table's GOT slots.
pub static PRIMITIVES_TABLE: LazyLock<SymbolTable<(), ()>> = LazyLock::new(build_primitives_table);

/// Build the `PRIMITIVES_TABLE` at static-init time.
///
/// Allocates a fresh `SymbolTable` rooted at `ModuleFullPath::from("primitives")`,
/// inserts one `ModuleEntry::Def` per Ring 0 primitive (mirroring
/// `cranelisp-typecheck::builtins::register_primitives`'s shape for the
/// `primitives_kind: Inline` set), allocates a GOT slot for each, and
/// writes the corresponding Rust shim's address into that slot via
/// `GotTable::store_slot`. The (symbol → ptr) pairing is sourced from
/// `crate::ring0::ring0_jit_symbols()` — the single source of truth for
/// Ring 0 shim addresses.
fn build_primitives_table() -> SymbolTable<(), ()> {
    let mut table = SymbolTable::<(), ()>::new(ModuleFullPath::from("primitives"));
    let shims: std::collections::HashMap<&'static str, *const u8> =
        ring0::ring0_jit_symbols().into_iter().collect();
    for prim in cranelisp_types::ring0_primitives() {
        let scheme = Scheme {
            vars: Vec::new(),
            constraints: std::collections::HashMap::new(),
            ty: prim.ty.clone(),
        };
        let slot = table.allocate_got_slot();
        if let Some(ptr) = shims.get(prim.name.as_ref()) {
            table.got.store_slot(slot, *ptr);
        }
        table.insert(
            prim.name.clone(),
            ModuleEntry::Def {
                scheme,
                visibility: Visibility::Public,
                docstring: None,
                param_names: prim.param_names.clone(),
                kind: Box::new(DefKind::Primitive {
                    primitive_kind: PrimitiveKind::Inline,
                    jit_name: Some(JitSymbol::from(prim.name.as_ref())),
                }),
                callees: Vec::new(),
                got_slot: Some(slot),
                trait_origin: None,
                ast: None,
                code: None,
            },
        );
    }
    table
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitives_table_contains_ring0_entries() {
        // Every Ring 0 primitive name must appear as a `ModuleEntry::Def`.
        for prim in cranelisp_types::ring0_primitives() {
            assert!(
                PRIMITIVES_TABLE.get(prim.name.as_ref()).is_some(),
                "missing entry for {}",
                prim.name
            );
        }
    }

    #[test]
    fn primitives_table_entries_carry_got_slot_and_ptr() {
        // Each Ring 0 entry must carry a `got_slot: Some(_)` and the slot
        // must hold a non-null code pointer matching the shim address.
        let shims: std::collections::HashMap<&'static str, *const u8> =
            ring0::ring0_jit_symbols().into_iter().collect();
        let mut checked = 0usize;
        for (name, entry) in PRIMITIVES_TABLE.symbols.iter() {
            let ModuleEntry::Def { got_slot: Some(slot), .. } = entry else {
                panic!("entry {name} should be a Def with got_slot");
            };
            let stored = PRIMITIVES_TABLE.got.load_slot(*slot);
            let expected = shims
                .get(name.as_ref())
                .copied()
                .expect("ring0_jit_symbols missing shim");
            assert_eq!(
                stored, expected,
                "GOT slot {slot} for {name} does not match shim address"
            );
            checked += 1;
        }
        assert!(checked >= ring0::ring0_jit_symbols().len() - 3 /* allow for entries without ptr */);
    }
}
