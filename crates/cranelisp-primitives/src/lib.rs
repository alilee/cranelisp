//! Cranelisp primitives — user-callable, symbol-table addressable operations.
//!
//! Per Decision 43 + Decision 48 (cross-surface narrative in
//! `bounded-contexts.md` §4a): this
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
//! `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>`. The ~22
//! individual extern fns demote to `pub(crate) extern "C"` carrying
//! `#[unsafe(export_name = "…")]`.
//!
//! DCE-survival of those extern fns in `--link`-mode static archives relies on
//! three existing mechanisms — there is **no `#[used] static` anchor**
//! (minimum mechanism, Principle 2): (1) the `#[unsafe(export_name = "…")]`
//! attribute emits the linker symbol into the object/staticlib independent of
//! the fn's Rust visibility (`pub(crate)` still yields the symbol); (2) the
//! exe-bundle force-link `LazyLock::force(&PRIMITIVES_TABLE)` at startup
//! (`cranelisp-exe-bundle/src/lib.rs:75`) is the link anchor that pulls the
//! static — and therefore the harvested fn addresses — into the binary;
//! (3) the in-crate `extern_shims()` harvest (below) takes every fn's address
//! at static-init, so each is referenced from live code. (`#[used]` is
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
//! that point on, primitives dispatch is functionally equivalent to any other
//! module via the standard cross-module GOT-indirect call sequence.
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
//! `LazyLock` owns the static fn addresses). The raw `*const u8` lives in the
//! `GotTable` indexed by `ModuleEntry::Def.got_slot` per Decision 35 ("GOT is
//! the single source of truth for callable addresses; no per-entry pointer
//! field") — invariant preserved trivially (there is no `code` payload).
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
//! "primitives reach code via GOT, never via direct extern" invariant
//! structurally per Principle 18 (bidirectional severance) and Principle 1
//! (decoupling).
//!
//! ## Module organisation
//!
//! Per-primitive-category sub-modules (`ring0`, `int`, `float`, `bool`,
//! `marshal`, `string`, `vec`) keep the source small and focused. Their
//! `extern "C"` members are `pub(crate)` carrying `#[unsafe(export_name)]`
//! (DCE survival via the export-name symbol + exe-bundle force-link +
//! `extern_shims()` harvest — see §"Public Rust API"); the only way for a
//! consumer outside the crate to reach a primitive's fn ptr is via
//! `PRIMITIVES_TABLE`'s GOT slots.
//!
//! Because every extern is `pub(crate)`, the `cargo-public-api` baseline
//! (`public-api.txt`) is **stable across primitive churn** — adding, renaming,
//! or deleting a primitive does not change the Rust public surface (the nine
//! lines: `PRIMITIVES_TABLE` + seven `pub mod` + the crate root). The semantic
//! surface — which primitives exist and their signatures — is governed by
//! **spec-conformance tests** (`/qa`, against `spec/appendix-a-builtins.md`
//! §A.2/§A.3) and the in-crate `operator::ring{0,1,3}_primitives()` builders
//! (the static-init content harness parity-checks builder → table), NOT by the
//! Rust baseline.

use std::collections::HashMap;
use std::sync::{Arc, LazyLock};

use cranelisp_types::{DefKind, ModuleEntry, ModuleFullPath, Scheme, SymbolTable};

pub mod bool;
pub mod float;
pub mod int;
pub mod marshal;
pub(crate) mod operator;
pub mod ring0;
pub mod string;
pub mod vec;

use operator::{PrimitiveDef, ring0_primitives, ring1_primitives, ring3_primitives};

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
/// process-static; all sessions read fn ptrs through the same atomic slots.
///
/// Population at static-init time: one `ModuleEntry::Def` per primitive in
/// the union of `ring0_primitives()` + `ring1_primitives()` +
/// `ring3_primitives()` + the static `vec-len` row. Each entry's `kind`
/// is the payload-free `DefKind::Primitive` unit variant (S69 Submission 36 —
/// the JIT linker name IS the symbol-table key, no `jit_name` field, no
/// `primitive_kind` sub-discriminator); `got_slot: Some(N)` indexes the GOT.
/// The corresponding `pub(crate) extern "C"` fn's address is stored at GOT
/// slot N via `table.got.store_slot(N, fn_ptr)`. Every entry carries
/// `code: None` (the `ModuleEntry::def(..).build()` default, FIXME 0244):
/// primitive-ness is read from `kind`, never from `code`. The (symbol → ptr)
/// mapping is built from a single in-crate harvest of every
/// `#[unsafe(export_name)]` extern fn across the submodules — see
/// `extern_shims()` below.
pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>> =
    LazyLock::new(|| Arc::new(build_primitives_table()));

/// Build the populated `SymbolTable<(), ()>` returned (wrapped in `Arc`)
/// from the `LazyLock` initialiser.
fn build_primitives_table() -> SymbolTable<(), ()> {
    let mut table = SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from("primitives"));
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
    // primitive — the Vec query family lives outside the ring tables). Insert
    // it with a hand-built scheme matching the source signature.
    insert_vec_len_entry(&mut table, &shims);

    table
}

/// Insert one `PrimitiveDef` into the table: allocate a GOT slot, store the
/// extern fn's address at that slot (when present in the shim harvest),
/// insert the `ModuleEntry::Def` with `kind: DefKind::Primitive` (and the
/// builder default `code: None`).
fn insert_primitive_entry(
    table: &mut SymbolTable<(), ()>,
    prim: &PrimitiveDef,
    shims: &HashMap<&'static str, *const u8>,
) {
    let slot = table.allocate_got_slot();
    if let Some(ptr) = shims.get(prim.name.as_ref()) {
        table.got.store_slot(slot, *ptr);
    }
    let scheme = Scheme {
        type_vars: Vec::new(),
        constraints: HashMap::new(),
        ty: prim.ty.clone(),
    };
    table.insert(
        prim.name.clone(),
        ModuleEntry::def(scheme, DefKind::Primitive)
            .param_names(prim.param_names.clone())
            .got_slot(slot)
            .build(),
    );
}

/// Insert the `vec-len` entry. Not in `ring{0,1,3}_primitives()` — the Vec
/// query family lives outside the ring tables.
fn insert_vec_len_entry(
    table: &mut SymbolTable<(), ()>,
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
        type_vars: Vec::new(),
        constraints: HashMap::new(),
        ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
    };
    table.insert(
        Symbol::from("vec-len"),
        ModuleEntry::def(scheme, DefKind::Primitive)
            .param_names(vec![Symbol::from("v")])
            .got_slot(slot)
            .build(),
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
    fn every_entry_is_def_kind_primitive() {
        // Decision 0048 (A2 reversed, FIXME 0244, 2026-05-31) — primitive-ness
        // is read from `kind: DefKind::Primitive` (the canonical fact), NOT
        // from `code`. Every entry carries the payload-free `DefKind::Primitive`
        // unit variant, and `code: None` (the `ModuleEntry::def(..).build()`
        // builder default; there is no `Code::Primitive` marker). The GOT
        // remains the single source of truth for the `*const u8` (Decision 35).
        for (name, entry) in PRIMITIVES_TABLE.symbols.iter() {
            let ModuleEntry::Def { kind, code, .. } = entry else {
                panic!("entry {name} should be a Def");
            };
            assert!(
                matches!(**kind, DefKind::Primitive),
                "entry {name} must carry DefKind::Primitive; got {kind:?}"
            );
            // Belt-and-suspenders: `code` is the builder default `None`
            // (no spec contract — `kind` is authoritative).
            assert!(
                code.is_none(),
                "entry {name} must carry code: None; got {code:?}"
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

    // -----------------------------------------------------------------------
    // Content harness (deliverable C(a)) — assert the spec contract
    // (`spec/appendix-a-builtins.md` §A.2/§A.3/§A.5) against each inserted
    // table entry. Parity-iterate the `ring{0,1,3}_primitives()` builders
    // (the constructor input) so the harness checks the insert path round-trips
    // builder input → table output, plus an explicit `vec-len` row.
    // -----------------------------------------------------------------------

    /// Assert one inserted entry against its expected `(ty, param_names)`.
    fn assert_content_row(name: &str, expected_ty: &cranelisp_types::Type, expected_params: &[&str]) {
        let entry = PRIMITIVES_TABLE
            .get(name)
            .unwrap_or_else(|| panic!("missing PRIMITIVES_TABLE entry for {name}"));
        let ModuleEntry::Def {
            scheme,
            param_names,
            got_slot,
            kind,
            ..
        } = entry
        else {
            panic!("entry {name} should be a Def");
        };
        // scheme.ty is the boundary Type::Fn per spec §A.3.
        assert_eq!(&scheme.ty, expected_ty, "scheme.ty mismatch for {name}");
        // param_names match the spec contract.
        let actual: Vec<&str> = param_names.iter().map(|p| p.as_ref()).collect();
        assert_eq!(actual.as_slice(), expected_params, "param_names mismatch for {name}");
        // got_slot is allocated.
        assert!(got_slot.is_some(), "entry {name} missing got_slot");
        // kind is the primitive discriminator.
        assert!(matches!(**kind, DefKind::Primitive), "entry {name} kind != Primitive");
        // jit_name IS the symbol-table key (S69 Submission 36) — pinned by the
        // successful `.get(name)` lookup above.
    }

    #[test]
    fn content_harness_ring_builders_round_trip() {
        // Parity check: every `PrimitiveDef` from the three ring builders
        // round-trips through the inserted `ModuleEntry::Def` — its
        // (name, ty, param_names) match the table entry. Catches insert-path
        // regressions (the builder is the source of the spec contract).
        let mut count = 0usize;
        for prim in ring0_primitives()
            .into_iter()
            .chain(ring1_primitives())
            .chain(ring3_primitives())
        {
            let params: Vec<&str> = prim.param_names.iter().map(|p| p.as_ref()).collect();
            assert_content_row(prim.name.as_ref(), &prim.ty, &params);
            count += 1;
        }
        // Sanity: the union is non-trivial (guards against an empty iterator
        // silently passing the loop).
        assert!(count >= 30, "expected >=30 ring-builder rows, got {count}");
    }

    #[test]
    fn content_harness_vec_len_row() {
        use cranelisp_types::Type;
        // `vec-len` is not in any ring builder — explicit row. Boundary scheme
        // is `(Fn [Int] Int)` (Vec erased to its i64 base-ptr ABI, Decision 11),
        // NOT the user-source `(Fn [(Vec a)] Int)`.
        assert_content_row(
            "vec-len",
            &Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            &["v"],
        );
    }

    // -----------------------------------------------------------------------
    // Behavioural harness (deliverable C(b)) — transmute-and-invoke the 20
    // PURE scalar ops (ring0 i64/f64 arithmetic+comparison, eq-bool, not)
    // against known I/O pairs. Heap/allocator-coupled ops are EXCLUDED (they
    // stay e2e / in string.rs + vec.rs module-local tests).
    // -----------------------------------------------------------------------

    /// Load the GOT-slot fn ptr for a primitive, asserting it is populated.
    fn slot_ptr(name: &str) -> *const u8 {
        let entry = PRIMITIVES_TABLE
            .get(name)
            .unwrap_or_else(|| panic!("missing entry for {name}"));
        let ModuleEntry::Def { got_slot: Some(slot), .. } = entry else {
            panic!("{name} must be a Def with got_slot");
        };
        let ptr = PRIMITIVES_TABLE.got.load_slot(*slot);
        assert!(!ptr.is_null(), "GOT slot for {name} is null");
        ptr
    }

    /// Invoke an `(i64, i64) -> i64` primitive by name.
    fn call_i64_i64(name: &str, a: i64, b: i64) -> i64 {
        // SAFETY: ptr is loaded from the GOT slot populated by extern_shims()
        // with the matching `extern "C" fn(i64, i64) -> i64`; we transmute back.
        let f: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(slot_ptr(name)) };
        f(a, b)
    }

    /// Invoke a `(i64) -> i64` primitive by name.
    fn call_i64(name: &str, a: i64) -> i64 {
        // SAFETY: as above, for `extern "C" fn(i64) -> i64`.
        let f: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(slot_ptr(name)) };
        f(a)
    }

    /// Invoke an `(f64, f64) -> f64` primitive by name (f64-bits ABI, Decision 10).
    fn call_f64_f64(name: &str, a: f64, b: f64) -> f64 {
        f64::from_bits(call_i64_i64(name, a.to_bits() as i64, b.to_bits() as i64) as u64)
    }

    /// Invoke an `(f64, f64) -> i64` comparison primitive (0/1).
    fn call_f64_cmp(name: &str, a: f64, b: f64) -> i64 {
        call_i64_i64(name, a.to_bits() as i64, b.to_bits() as i64)
    }

    #[test]
    fn behavioural_ring0_int_arithmetic() {
        // spec: appendix-a-builtins §A.2 — int arithmetic.
        assert_eq!(call_i64_i64("add-i64", 2, 3), 5);
        assert_eq!(call_i64_i64("sub-i64", 7, 4), 3);
        assert_eq!(call_i64_i64("mul-i64", 6, 7), 42);
        // div-i64: only the non-zero happy path here (div-by-zero panic path
        // is e2e — couples to the intrinsics thread-local error slot).
        assert_eq!(call_i64_i64("div-i64", 6, 2), 3);
    }

    #[test]
    fn behavioural_ring0_int_comparison() {
        // spec: appendix-a-builtins §A.2 — int comparison (0/1).
        assert_eq!(call_i64_i64("eq-i64", 3, 3), 1);
        assert_eq!(call_i64_i64("eq-i64", 3, 4), 0);
        assert_eq!(call_i64_i64("lt-i64", 2, 3), 1);
        assert_eq!(call_i64_i64("lt-i64", 3, 2), 0);
        assert_eq!(call_i64_i64("gt-i64", 3, 2), 1);
        assert_eq!(call_i64_i64("gt-i64", 2, 3), 0);
        assert_eq!(call_i64_i64("le-i64", 3, 3), 1);
        assert_eq!(call_i64_i64("le-i64", 4, 3), 0);
        assert_eq!(call_i64_i64("ge-i64", 3, 3), 1);
        assert_eq!(call_i64_i64("ge-i64", 2, 3), 0);
    }

    #[test]
    fn behavioural_ring0_float_arithmetic() {
        // spec: appendix-a-builtins §A.2 — float arithmetic (f64-bits ABI).
        assert_eq!(call_f64_f64("add-f64", 1.5, 2.5), 4.0);
        assert_eq!(call_f64_f64("sub-f64", 5.0, 1.5), 3.5);
        assert_eq!(call_f64_f64("mul-f64", 2.0, 3.5), 7.0);
        assert_eq!(call_f64_f64("div-f64", 9.0, 3.0), 3.0);
    }

    #[test]
    fn behavioural_ring0_float_comparison() {
        // spec: appendix-a-builtins §A.2 — float comparison (0/1).
        assert_eq!(call_f64_cmp("eq-f64", 1.5, 1.5), 1);
        assert_eq!(call_f64_cmp("eq-f64", 1.5, 2.5), 0);
        assert_eq!(call_f64_cmp("lt-f64", 1.0, 2.0), 1);
        assert_eq!(call_f64_cmp("lt-f64", 2.0, 1.0), 0);
        assert_eq!(call_f64_cmp("gt-f64", 2.0, 1.0), 1);
        assert_eq!(call_f64_cmp("gt-f64", 1.0, 2.0), 0);
        assert_eq!(call_f64_cmp("le-f64", 1.5, 1.5), 1);
        assert_eq!(call_f64_cmp("le-f64", 2.0, 1.5), 0);
        assert_eq!(call_f64_cmp("ge-f64", 1.5, 1.5), 1);
        assert_eq!(call_f64_cmp("ge-f64", 1.0, 1.5), 0);
    }

    #[test]
    fn behavioural_ring0_boolean() {
        // spec: appendix-a-builtins §A.3 — not (Decision 0048 C1) + eq-bool.
        assert_eq!(call_i64("not", 0), 1, "(not false) = true");
        assert_eq!(call_i64("not", 1), 0, "(not true) = false");
        assert_eq!(call_i64_i64("eq-bool", 1, 1), 1);
        assert_eq!(call_i64_i64("eq-bool", 1, 0), 0);
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
