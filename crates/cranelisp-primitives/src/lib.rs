//! Cranelisp primitives — user-callable, symbol-table addressable operations.
//!
//! Per Decision 43 + Decision 48 + `design/arch/facades/primitives.md`: this
//! crate hosts the kebab-case, user-addressable primitives whose JIT names
//! appear in the synthetic `primitives` module's symbol table (e.g. `add-i64`,
//! `str-concat`, `vec-len`, `substring`, `int-to-string`, `parse-int`,
//! `float-to-string`, `bool-to-string`, `sconcat`, `quote-sexp`, `not`). The
//! sibling crate `cranelisp-intrinsics` hosts the backend-emitted-call
//! targets (`runtime/alloc`, `runtime/dealloc`, `runtime/panic`, RC
//! primitives, drop glue, the IO trampoline) — those are the codegen-coupled
//! implementation substrate; this crate is the spec-driven user surface.
//!
//! ## Public Rust API — single item
//!
//! Per Decision 0048 (S68): the public Rust surface is the single static
//! `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>`. The ~22
//! individual extern fns demote to `pub(crate) extern "C"` with `#[used]`
//! discipline (to prevent DCE in `--link`-mode static archives). The
//! statically-constructed `Arc<SymbolTable>` is Arc-cloned into each
//! `CompilerSession`'s `SymbolTables<Code, ()>` map at session init — from
//! that point on, primitives dispatch is functionally equivalent to any
//! other module via the standard cross-module GOT-indirect call sequence.
//!
//! ## Lifecycle marker — `Code::Primitive`
//!
//! Every `ModuleEntry::Def.code = Some(Code::Primitive)` per Decision 0048
//! §"Shape" (S68 Phase 3 user revision, 2026-05-17). The marker variant
//! carries no payload — Decision 35's "GOT is the single source of truth
//! for callable addresses; no per-entry pointer field" invariant is
//! preserved. The fn ptr lives in the per-module `GotTable` indexed by
//! `ModuleEntry::Def.got_slot`; the `Code::Primitive` marker expresses the
//! *lifecycle category* (process-static, externally owned by this
//! `LazyLock`) at every match site over `Code`.
//!
//! ## Backend dep-ban (Decision 0048 §"Structural invariant")
//!
//! `cranelisp-backend` MUST NOT depend on `cranelisp-primitives`. The
//! reverse edge — `cranelisp-primitives → cranelisp-backend` — is permitted
//! and required (for the `Code::Primitive` marker variant). The workspace
//! DAG enforces the "primitives reach code via GOT, never via direct extern"
//! invariant structurally per Principle 18.
//!
//! ## Module organisation
//!
//! Per-primitive-category sub-modules (`ring0`, `int`, `float`, `bool`,
//! `marshal`, `string`, `vec`) keep the source small and focused. Their
//! `extern "C"` members are `pub(crate)` with `#[used]`; the only way for
//! a consumer outside the crate to reach a primitive's fn ptr is via
//! `PRIMITIVES_TABLE`'s GOT slots.

use std::collections::HashMap;
use std::sync::{Arc, LazyLock};

use cranelisp_backend::Code;
use cranelisp_types::{
    DefKind, JitSymbol, ModuleEntry, ModuleFullPath, PrimitiveDef, PrimitiveKind, Scheme,
    SymbolTable, Visibility, ring0_primitives, ring1_primitives, ring3_primitives,
};

pub mod bool;
pub mod float;
pub mod int;
pub mod marshal;
pub mod ring0;
pub mod string;
pub mod vec;

/// The synthetic `primitives` module's statically-constructed symbol table
/// and GOT.
///
/// Per Decision 0048 §"Shape": `LazyLock<Arc<SymbolTable<Code, ()>>>`. The
/// `Arc` outer is what CompilerSession Arc-clones into `session.symbol_tables`
/// at init — one Arc-share per session, all pointing at the same static
/// `SymbolTable`. The inner `Arc<GotTable>` (via `SymbolTable.got`) is
/// likewise process-static; all sessions read fn ptrs through the same
/// atomic slots.
///
/// Population at static-init time: one `ModuleEntry::Def` per primitive in
/// the union of `ring0_primitives()` + `ring1_primitives()` +
/// `ring3_primitives()` + the static `vec-len` row. Each entry's `kind`
/// is `DefKind::Primitive { primitive_kind: PrimitiveKind::Inline,
/// jit_name: Some(JitSymbol::from(name)) }`; `got_slot: Some(N)` indexes
/// the GOT. The corresponding `pub(crate) extern "C"` fn's address is
/// stored at GOT slot N via `table.got.store_slot(N, fn_ptr)`. Every entry
/// carries `code: Some(Code::Primitive)` per Decision 0048 A2 (revised
/// 2026-05-17): the marker variant expresses process-static lifecycle.
/// The (symbol → ptr) mapping is built from a single in-crate harvest of
/// every `#[unsafe(export_name)]` extern fn across the submodules — see
/// `extern_shims()` below.
pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>> =
    LazyLock::new(|| Arc::new(build_primitives_table()));

/// Build the populated `SymbolTable<Code, ()>` returned (wrapped in `Arc`)
/// from the `LazyLock` initialiser.
fn build_primitives_table() -> SymbolTable<Code, ()> {
    let mut table = SymbolTable::<Code, ()>::new_with_params(ModuleFullPath::from("primitives"));
    let shims = extern_shims();

    // Union the three primitive registries from `cranelisp-types`.
    let mut all_prims: Vec<PrimitiveDef> = Vec::new();
    all_prims.extend(ring0_primitives());
    all_prims.extend(ring1_primitives());
    all_prims.extend(ring3_primitives());

    for prim in &all_prims {
        insert_primitive_entry(&mut table, prim, &shims);
    }

    // `vec-len` is not in any of the three registry fns (it's a vec query
    // primitive — see `facades/primitives.md` §"Vec query"). Insert it
    // with a hand-built scheme matching the source signature.
    insert_vec_len_entry(&mut table, &shims);

    table
}

/// Insert one `PrimitiveDef` into the table: allocate a GOT slot, store the
/// extern fn's address at that slot (when present in the shim harvest),
/// insert the `ModuleEntry::Def` with `code: Some(Code::Primitive)`.
fn insert_primitive_entry(
    table: &mut SymbolTable<Code, ()>,
    prim: &PrimitiveDef,
    shims: &HashMap<&'static str, *const u8>,
) {
    let slot = table.allocate_got_slot();
    if let Some(ptr) = shims.get(prim.name.as_ref()) {
        table.got.store_slot(slot, *ptr);
    }
    let scheme = Scheme {
        vars: Vec::new(),
        constraints: HashMap::new(),
        ty: prim.ty.clone(),
    };
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
            code: Some(Code::Primitive),
        },
    );
}

/// Insert the `vec-len` entry. Not in `ring{0,1,3}_primitives()` — the Vec
/// query family lives outside the ring tables in
/// `facades/primitives.md` §"Vec query".
fn insert_vec_len_entry(
    table: &mut SymbolTable<Code, ()>,
    shims: &HashMap<&'static str, *const u8>,
) {
    use cranelisp_types::{Symbol, Type};
    let slot = table.allocate_got_slot();
    if let Some(ptr) = shims.get("vec-len") {
        table.got.store_slot(slot, *ptr);
    }
    // `vec-len :: (Fn [Int] Int)` at the boundary scheme. The user-source
    // type is `(Fn [(Vec a)] Int)`; the primitive-table boundary erases
    // the Vec to its i64 base-ptr ABI per Decision 11.
    let scheme = Scheme {
        vars: Vec::new(),
        constraints: HashMap::new(),
        ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
    };
    table.insert(
        Symbol::from("vec-len"),
        ModuleEntry::Def {
            scheme,
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![Symbol::from("v")],
            kind: Box::new(DefKind::Primitive {
                primitive_kind: PrimitiveKind::Inline,
                jit_name: Some(JitSymbol::from("vec-len")),
            }),
            callees: Vec::new(),
            got_slot: Some(slot),
            trait_origin: None,
            ast: None,
            code: Some(Code::Primitive),
        },
    );
}

/// Harvest of every `#[unsafe(export_name = "…")] pub(crate) extern "C" fn`
/// across the per-category submodules. Single source of truth for the
/// (kebab-case symbol name → raw fn ptr) mapping populated into the GOT at
/// static-init.
fn extern_shims() -> HashMap<&'static str, *const u8> {
    let mut m: HashMap<&'static str, *const u8> = HashMap::new();

    // Ring 0 — arithmetic/comparison/boolean (23 entries; includes `not`).
    m.insert("add-i64", ring0::add_i64 as *const u8);
    m.insert("sub-i64", ring0::sub_i64 as *const u8);
    m.insert("mul-i64", ring0::mul_i64 as *const u8);
    m.insert("div-i64", ring0::div_i64 as *const u8);
    m.insert("add-f64", ring0::add_f64 as *const u8);
    m.insert("sub-f64", ring0::sub_f64 as *const u8);
    m.insert("mul-f64", ring0::mul_f64 as *const u8);
    m.insert("div-f64", ring0::div_f64 as *const u8);
    m.insert("eq-i64", ring0::eq_i64 as *const u8);
    m.insert("lt-i64", ring0::lt_i64 as *const u8);
    m.insert("gt-i64", ring0::gt_i64 as *const u8);
    m.insert("le-i64", ring0::le_i64 as *const u8);
    m.insert("ge-i64", ring0::ge_i64 as *const u8);
    m.insert("neq-i64", ring0::neq_i64 as *const u8);
    m.insert("eq-f64", ring0::eq_f64 as *const u8);
    m.insert("lt-f64", ring0::lt_f64 as *const u8);
    m.insert("gt-f64", ring0::gt_f64 as *const u8);
    m.insert("le-f64", ring0::le_f64 as *const u8);
    m.insert("ge-f64", ring0::ge_f64 as *const u8);
    m.insert("neq-f64", ring0::neq_f64 as *const u8);
    m.insert("not", ring0::not as *const u8);
    m.insert("eq-bool", ring0::eq_bool as *const u8);
    m.insert("neq-bool", ring0::neq_bool as *const u8);

    // Int — int-to-string, parse-int.
    m.insert("int-to-string", int::int_to_string as *const u8);
    m.insert("parse-int", int::parse_int as *const u8);

    // Float — float-to-string.
    m.insert("float-to-string", float::float_to_string as *const u8);

    // Bool — bool-to-string.
    m.insert("bool-to-string", bool::bool_to_string as *const u8);

    // Marshal — sconcat, quote-sexp.
    m.insert("sconcat", marshal::sconcat as *const u8);
    m.insert("quote-sexp", marshal::quote_sexp as *const u8);

    // String — full set.
    m.insert("str-concat", string::str_concat as *const u8);
    m.insert("str-eq", string::str_eq as *const u8);
    m.insert("str-len", string::str_len as *const u8);
    m.insert("string-identity", string::string_identity as *const u8);
    m.insert("substring", string::str_substring as *const u8);
    m.insert("char-at", string::str_char_at as *const u8);
    m.insert("split", string::str_split as *const u8);
    m.insert("join", string::str_join as *const u8);
    m.insert("replace", string::str_replace as *const u8);
    m.insert("trim", string::str_trim as *const u8);
    m.insert("starts-with?", string::str_starts_with as *const u8);
    m.insert("ends-with?", string::str_ends_with as *const u8);
    m.insert("contains?", string::str_contains as *const u8);
    m.insert("to-upper", string::str_to_upper as *const u8);
    m.insert("to-lower", string::str_to_lower as *const u8);

    // Vec — vec-len.
    m.insert("vec-len", vec::vec_len as *const u8);

    m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitives_table_contains_ring0_entries() {
        // Every Ring 0 primitive name must appear as a `ModuleEntry::Def`.
        for prim in ring0_primitives() {
            assert!(
                PRIMITIVES_TABLE.get(prim.name.as_ref()).is_some(),
                "missing entry for {}",
                prim.name
            );
        }
    }

    #[test]
    fn primitives_table_contains_ring1_entries() {
        for prim in ring1_primitives() {
            assert!(
                PRIMITIVES_TABLE.get(prim.name.as_ref()).is_some(),
                "missing entry for {}",
                prim.name
            );
        }
    }

    #[test]
    fn primitives_table_contains_ring3_entries() {
        for prim in ring3_primitives() {
            assert!(
                PRIMITIVES_TABLE.get(prim.name.as_ref()).is_some(),
                "missing entry for {}",
                prim.name
            );
        }
    }

    #[test]
    fn primitives_table_contains_vec_len() {
        assert!(PRIMITIVES_TABLE.get("vec-len").is_some());
    }

    #[test]
    fn primitives_table_is_non_empty_with_expected_minimum() {
        // ring0 (20) + ring1 (~17) + ring3 (1) + vec-len (1) = ~39.
        // Hold the floor at 30 to absorb small registry churn without
        // requiring this test to track an exact count.
        assert!(
            PRIMITIVES_TABLE.symbols.len() >= 30,
            "expected at least 30 entries, got {}",
            PRIMITIVES_TABLE.symbols.len(),
        );
    }

    #[test]
    fn every_entry_carries_got_slot() {
        for (name, entry) in PRIMITIVES_TABLE.symbols.iter() {
            let ModuleEntry::Def { got_slot, .. } = entry else {
                panic!("entry {name} should be a Def");
            };
            assert!(
                got_slot.is_some(),
                "entry {name} missing got_slot"
            );
        }
    }

    #[test]
    fn every_entry_carries_code_primitive_marker() {
        // Decision 0048 §"Shape" (S68 Phase 3 amendment, 2026-05-17 user
        // revision) — every primitives `ModuleEntry::Def.code` MUST be
        // `Some(Code::Primitive)`. The marker variant expresses the
        // process-static lifecycle category at every match site over
        // `Code`; it carries no payload (Decision 35 invariant preserved —
        // the GOT remains the single source of truth for the `*const u8`).
        for (name, entry) in PRIMITIVES_TABLE.symbols.iter() {
            let ModuleEntry::Def { code, .. } = entry else {
                panic!("entry {name} should be a Def");
            };
            assert!(
                matches!(code, Some(Code::Primitive)),
                "entry {name} must carry Code::Primitive; got {:?}",
                code
            );
        }
    }

    #[test]
    fn got_slots_hold_extern_ptrs_for_harvested_shims() {
        // For each entry whose name appears in the shim harvest, the GOT
        // slot must hold the matching fn pointer.
        let shims = extern_shims();
        for (name, entry) in PRIMITIVES_TABLE.symbols.iter() {
            let ModuleEntry::Def { got_slot: Some(slot), .. } = entry else {
                panic!("entry {name} should be a Def with got_slot");
            };
            let stored = PRIMITIVES_TABLE.got.load_slot(*slot);
            if let Some(expected) = shims.get(name.as_ref()) {
                assert_eq!(
                    stored, *expected,
                    "GOT slot {slot} for {name} does not match shim address"
                );
                assert!(!stored.is_null(), "GOT slot {slot} for {name} is null");
            }
        }
    }

    #[test]
    fn not_primitive_present_and_callable() {
        // Decision 0048 (C1) + spec/appendix-a-builtins.md §A.3.
        let entry = PRIMITIVES_TABLE
            .get("not")
            .expect("`not` must be a primitives entry");
        let ModuleEntry::Def { got_slot: Some(slot), .. } = entry else {
            panic!("`not` must be a Def with got_slot");
        };
        let ptr = PRIMITIVES_TABLE.got.load_slot(*slot);
        assert!(!ptr.is_null(), "`not` GOT slot is null");
        // SAFETY: `ptr` was just loaded from a slot populated by
        // `extern_shims()` with `ring0::not as *const u8`. The shim's
        // signature is `extern "C" fn(i64) -> i64`. We transmute back.
        let not_fn: extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(ptr) };
        assert_eq!(not_fn(0), 1, "(not false) = true");
        assert_eq!(not_fn(1), 0, "(not true) = false");
    }

    #[test]
    fn extern_shims_harvest_covers_full_inventory() {
        // Sanity check on the extern_shims() harvest: every shim name must
        // be present as a primitives entry OR be one of the known
        // out-of-table extern shims (reachable via the harvest for GOT
        // population from other modules, but not registered in
        // `PRIMITIVES_TABLE` itself):
        //
        // - `neq-i64` / `neq-f64` / `neq-bool` — reachable through
        //   trait-method resolution (`Eq.!=`), not surfaced as entries
        //   in the typecheck-side `ring0_primitives()` table.
        // - `sconcat` — registered in the synthetic `macros` module per
        //   `spec/09-macros.md`, not in `primitives`.
        for name in extern_shims().keys() {
            assert!(
                PRIMITIVES_TABLE.get(name).is_some()
                    || matches!(
                        *name,
                        "neq-i64" | "neq-f64" | "neq-bool" | "sconcat"
                    ),
                "shim {name} has no PRIMITIVES_TABLE entry"
            );
        }
    }
}
