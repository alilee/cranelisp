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
use std::sync::atomic::AtomicPtr;
use std::sync::{Arc, LazyLock};

use cranelisp_types::{
    DefKind, GOT_TABLE_SIZE, GotTable, ModuleEntry, ModuleFullPath, Scheme, SymbolTable,
};

/// The writable static slab backing the synthetic `primitives` module's GOT,
/// exported under the canonical link-time symbol `__cranelisp_got_primitives`.
///
/// Per FIXME 0280 (Decision 0048): every extern-primitive call site emits
/// GOT-indirect dispatch against `__cranelisp_got_primitives` in ALL modes
/// (`apply.rs`). User/stdlib modules' GOTs are link-time data symbols in object
/// mode (`define_module_got_data`); the primitives GOT must be one too, or
/// `--link` binaries fail at `ld` ("symbol not found: ___cranelisp_got_primitives").
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
/// forces `PRIMITIVES_TABLE`'s `LazyLock` before user code runs, populating the
/// slab's slots with the harvested extern fn addresses.
#[unsafe(export_name = "__cranelisp_got_primitives")]
pub static PRIMITIVES_GOT_SLAB: [AtomicPtr<u8>; GOT_TABLE_SIZE] =
    [const { AtomicPtr::new(std::ptr::null_mut()) }; GOT_TABLE_SIZE];

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
/// `ring3_primitives()` + the four static Vec-query rows (`vec-get`,
/// `vec-set`, `vec-push`, `vec-len`). Each entry's `kind`
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

    // Replace the default heap GOT (from `new_with_params`) with one
    // constructed over the exported static slab `__cranelisp_got_primitives`
    // (FIXME 0280). This makes the primitives GOT base a link-time symbol, so
    // `--link`-mode extern-primitive dispatch resolves at `ld` time. The slab
    // is process-static; exactly one `GotTable` is built over it here.
    table.got = Arc::new(GotTable::with_static_backing(&PRIMITIVES_GOT_SLAB));

    let shims = extern_shims();

    // Union the three primitive registries from `cranelisp-types`.
    let mut all_prims: Vec<PrimitiveDef> = Vec::new();
    all_prims.extend(ring0_primitives());
    all_prims.extend(ring1_primitives());
    all_prims.extend(ring3_primitives());

    for prim in &all_prims {
        insert_primitive_entry(&mut table, prim, &shims);
    }

    // The Vec query family (`vec-get`/`vec-set`/`vec-push`/`vec-len`) is not
    // in any of the three registry fns — these primitives live outside the
    // ring tables. Insert them with hand-built polymorphic schemes matching
    // the appendix-A source signatures.
    insert_vec_query_entries(&mut table, &shims);

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
        ModuleEntry::def(scheme, DefKind::Primitive { got_slot: slot })
            .param_names(prim.param_names.clone())
            .docstring(prim.docstring)
            .build(),
    );
}

/// Insert the Vec query family — `vec-get`, `vec-set`, `vec-push`, `vec-len`.
///
/// None of these are in `ring{0,1,3}_primitives()`; the Vec query family lives
/// outside the ring tables. Each carries the **polymorphic** appendix-A scheme
/// (`spec/appendix-a-builtins.md` §A.3) over a single quantified element type
/// var `a`, NOT a boundary-erased monomorphic scheme: the user-source argument
/// is an actual `(Vec a)` value, so the resolved type must unify with one (an
/// erased `(Fn [Int] …)` scheme fails to unify against a `(Vec Int)` argument
/// at the call site).
///
/// The backend compiles applications of all four inline (`compile_vec_get`,
/// `compile_vec_set`, `compile_vec_push`, `compile_vec_len` in
/// `cranelisp-backend::compiler::vec_codegen`) keyed by the primitive name, so
/// the GOT slot is only ever consulted for `vec-len` (the one op carrying an
/// `extern "C"` fallback shim, [`vec::vec_len`]); `vec-get`/`vec-set`/`vec-push`
/// have no extern body and their GOT slots stay null — name resolution is the
/// sole gap these entries close.
///
/// The quantified-var `TypeId` value is arbitrary: `instantiate` remaps every
/// scheme's `type_vars` to fresh ids on use, so the constant `0` here cannot
/// collide with any other scheme's vars.
fn insert_vec_query_entries(
    table: &mut SymbolTable<(), ()>,
    shims: &HashMap<&'static str, *const u8>,
) {
    use cranelisp_types::{ModuleFullPath, Symbol, Type, TypeName};

    // The single quantified element-type var `a`, shared by all four schemes.
    const A: cranelisp_types::TypeId = 0;
    let vec_a = || {
        Type::adt(
            ModuleFullPath::from("primitives"),
            TypeName::from("Vec"),
            vec![Type::Var(A)],
        )
    };

    // (name, scheme-ty, param_names, docstring). Polymorphic over `a` (§A.3);
    // docstring is the §A.3 Description-column text (§A.5 MUST).
    let entries: Vec<(&str, Type, Vec<Symbol>, &'static str)> = vec![
        // vec-get :: forall a. (Fn [(Vec a) Int] a)
        (
            "vec-get",
            Type::Fn(vec![vec_a(), Type::Int], Box::new(Type::Var(A))),
            vec![Symbol::from("v"), Symbol::from("idx")],
            "Index (bounds-checked; panics on out-of-bounds)",
        ),
        // vec-set :: forall a. (Fn [(Vec a) Int a] (Vec a))
        (
            "vec-set",
            Type::Fn(vec![vec_a(), Type::Int, Type::Var(A)], Box::new(vec_a())),
            vec![Symbol::from("v"), Symbol::from("idx"), Symbol::from("val")],
            "Return new Vec with element at index replaced",
        ),
        // vec-push :: forall a. (Fn [(Vec a) a] (Vec a))
        (
            "vec-push",
            Type::Fn(vec![vec_a(), Type::Var(A)], Box::new(vec_a())),
            vec![Symbol::from("v"), Symbol::from("val")],
            "Return new Vec with element appended",
        ),
        // vec-len :: forall a. (Fn [(Vec a)] Int)
        (
            "vec-len",
            Type::Fn(vec![vec_a()], Box::new(Type::Int)),
            vec![Symbol::from("v")],
            "Number of elements",
        ),
    ];

    for (name, ty, param_names, docstring) in entries {
        let slot = table.allocate_got_slot();
        if let Some(ptr) = shims.get(name) {
            table.got.store_slot(slot, *ptr);
        }
        let scheme = Scheme {
            type_vars: vec![A],
            constraints: HashMap::new(),
            ty,
        };
        table.insert(
            Symbol::from(name),
            ModuleEntry::def(scheme, DefKind::Primitive { got_slot: slot })
                .param_names(param_names)
                .docstring(docstring)
                .build(),
        );
    }
}

/// Harvest of every `#[unsafe(export_name = "…")] pub(crate) extern "C" fn`
/// across the per-category submodules. Single source of truth for the
/// (kebab-case symbol name → raw fn ptr) mapping populated into the GOT at
/// static-init.
fn extern_shims() -> HashMap<&'static str, *const u8> {
    let mut m: HashMap<&'static str, *const u8> = HashMap::new();

    // Ring 0 — arithmetic/comparison/boolean (23 entries; includes `not`)
    // plus the 7 bitwise ops (FIXME 0416, S91) registered below.
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

    // Bitwise integer operations (FIXME 0416, S91).
    m.insert("bit-and", ring0::bit_and as *const u8);
    m.insert("bit-or", ring0::bit_or as *const u8);
    m.insert("bit-xor", ring0::bit_xor as *const u8);
    m.insert("bit-not", ring0::bit_not as *const u8);
    m.insert("shl", ring0::shl as *const u8);
    m.insert("shr", ring0::shr as *const u8);
    m.insert("popcount", ring0::popcount as *const u8);

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
    m.insert("neq-string", string::neq_string as *const u8);
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
mod tests;
