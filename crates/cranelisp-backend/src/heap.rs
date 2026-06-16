//! Heap layout types, RC emit helpers, and codegen heap classification.
//!
//! This module is the SOLE location that imports the cross-crate layout
//! constants (`HeapHeader`, `HeapAdt`, `HeapClosure` offsets — the runtime
//! layout contract intrinsics and codegen agree on). All other codegen code
//! calls these helpers, confining heap-layout assumptions per
//! `src/CLAUDE.md` §"Heap Access". These items are `pub` because
//! `cranelisp-intrinsics` reads the layouts and codegen emits offset-keyed
//! loads against the same constants; no external consumer should call the emit
//! helpers.
//!
//! [`HeapCategory`] + [`HeapCategory::classify`] are backend-internal codegen
//! classification (relocated here from `cranelisp-types` per S69 Sub 38 — zero
//! production consumers outside this crate). `classify` carries an interim
//! two-mode `Option<&tables>` contract (pre-typecheck: ADTs conservatively
//! `Mixed`; post-typecheck: classified by constructor inspection) and several
//! pending structural cascades noted at the item.
//!
//! Contents:
//!   - `HeapAdt` — ADT data-constructor layout
//!   - `HeapClosure` — closure layout
//!   - `heap_load` / `heap_store` — load/store an i64 from/into a heap object
//!   - `emit_rc_inc` — inline atomic RC increment
//!   - `emit_rc_dec` — inline atomic RC decrement + conditional dealloc
//!   - `emit_alloc` — emit call to `runtime/alloc`

use std::collections::HashMap;
use std::mem::{self, offset_of};

use cranelift::prelude::*;
use cranelift_codegen::ir::AtomicRmwOp;
use cranelift_module::{FuncId, Module};

use dashmap::DashMap;

use cranelisp_types::{
    FQTypeName, HeapHeader, ModuleEntry, ModuleFullPath, Symbol, SymbolTable, Type,
};

use crate::codegen_types::NULLARY_TAG_THRESHOLD;

// ---------------------------------------------------------------------------
// Heap layout structs — backend-owned
// ---------------------------------------------------------------------------

/// ADT data constructor: [header | tag | field_0 | field_1 | ... | field_n]
/// Nullary constructors are NOT heap-allocated — they are bare i64 tags.
#[repr(C)]
pub struct HeapAdt {
    pub header: HeapHeader,
    /// Constructor tag (same tag value whether nullary or data constructor).
    pub tag: i64,
    // Fields follow at FIELDS_START. Each field is an i64.
}

impl HeapAdt {
    pub const TAG_OFFSET: i32 = offset_of!(Self, tag) as i32; // 16
    pub const FIELDS_START: usize = mem::size_of::<Self>(); // 24

    /// Offset of the i-th field from the base pointer.
    pub const fn field_offset(i: usize) -> i32 {
        (Self::FIELDS_START + i * mem::size_of::<i64>()) as i32
    }

    /// Payload size after the header: tag + n fields.
    pub const fn payload_size(field_count: usize) -> usize {
        mem::size_of::<i64>() + field_count * mem::size_of::<i64>()
    }
}

const _: () = assert!(HeapAdt::TAG_OFFSET == 16);
const _: () = assert!(HeapAdt::FIELDS_START == 24);

/// Closure: [header | code_ptr | drop_glue_ptr | cap_0 | cap_1 | ... | cap_n]
///
/// `drop_glue_ptr` is 0 for closures with no heap-typed captures.
/// When non-zero, it points to a `(ptr: i64) -> ()` function that dec's
/// each captured heap value before the closure env is freed.
#[repr(C)]
pub struct HeapClosure {
    pub header: HeapHeader,
    /// Pointer to the compiled lambda body.
    /// Lambda body signature: (env_ptr: i64, params...) -> i64
    pub code_ptr: i64,
    /// Pointer to the drop glue function for captured heap values.
    /// Zero if no captures are heap-typed.
    /// Drop glue signature: (closure_ptr: i64) -> ()
    pub drop_glue_ptr: i64,
    // Captures follow at CAPTURES_START. Each capture is an i64.
}

impl HeapClosure {
    pub const CODE_PTR_OFFSET: i32 = offset_of!(Self, code_ptr) as i32; // 16
    pub const DROP_GLUE_PTR_OFFSET: i32 = offset_of!(Self, drop_glue_ptr) as i32; // 24
    pub const CAPTURES_START: usize = mem::size_of::<Self>(); // 32

    /// Offset of the i-th captured value from the base pointer.
    pub const fn capture_offset(i: usize) -> i32 {
        (Self::CAPTURES_START + i * mem::size_of::<i64>()) as i32
    }

    /// Payload size after the header: code_ptr + drop_glue_ptr + n captures.
    pub const fn payload_size(capture_count: usize) -> usize {
        2 * mem::size_of::<i64>() + capture_count * mem::size_of::<i64>()
    }
}

const _: () = assert!(HeapClosure::CODE_PTR_OFFSET == 16);
const _: () = assert!(HeapClosure::DROP_GLUE_PTR_OFFSET == 24);
const _: () = assert!(HeapClosure::CAPTURES_START == 32);

/// Vec: [header | len | cap | data_ptr]
/// The data buffer is a separate allocation: [elem_0 | elem_1 | ... | elem_{cap-1}]
/// Each element is i64 (uniform representation). Only the first `len` elements are live.
#[repr(C)]
pub struct HeapVec {
    pub header: HeapHeader,
    /// Number of live elements (0..len are initialized).
    pub len: i64,
    /// Capacity of the data buffer (in elements, not bytes).
    pub cap: i64,
    /// Pointer to the data buffer. The buffer holds `cap` slots of i64.
    pub data_ptr: i64, // ptr-width: i64 on native
}

impl HeapVec {
    pub const LEN_OFFSET: i32 = offset_of!(Self, len) as i32;           // 16
    pub const CAP_OFFSET: i32 = offset_of!(Self, cap) as i32;           // 24
    pub const DATA_PTR_OFFSET: i32 = offset_of!(Self, data_ptr) as i32; // 32

    /// Payload size after the header: len + cap + data_ptr.
    pub const fn payload_size() -> usize {
        3 * mem::size_of::<i64>()  // 24 bytes
    }
}

const _: () = assert!(HeapVec::LEN_OFFSET == 16);
const _: () = assert!(HeapVec::CAP_OFFSET == 24);
const _: () = assert!(HeapVec::DATA_PTR_OFFSET == 32);
const _: () = assert!(mem::size_of::<HeapVec>() == 40);

// ---------------------------------------------------------------------------
// Generic heap access helpers — free functions
// ---------------------------------------------------------------------------

/// Load an i64 value from a heap object at the given byte offset.
///
/// The offset MUST come from a layout constant (HeapHeader::RC_OFFSET,
/// HeapAdt::field_offset(i), etc.) — never a bare numeric literal.
///
/// ptr is ptr-width (i64 on native); the returned value is data-width (i64).
// Narrowed to `pub(crate)` in S75 W3 — per-call-site codegen primitive; in-crate only.
pub(crate) fn heap_load(builder: &mut FunctionBuilder, ptr: Value, offset: i32) -> Value {
    builder
        .ins()
        .load(types::I64, MemFlags::trusted(), ptr, offset)
}

/// Store an i64 value into a heap object at the given byte offset.
/// Same offset rules as heap_load.
pub(crate) fn heap_store(builder: &mut FunctionBuilder, val: Value, ptr: Value, offset: i32) {
    builder.ins().store(MemFlags::trusted(), val, ptr, offset);
}

// ---------------------------------------------------------------------------
// RC emission helpers
// ---------------------------------------------------------------------------

/// Emit inline atomic RC increment.
///
/// Cranelift atomic_rmw(Add, ptr + RC_OFFSET, 1, Release).
/// This is an INLINE atomic op, NOT an extern function call.
pub(crate) fn emit_rc_inc(builder: &mut FunctionBuilder, ptr: Value) {
    let rc_addr = builder
        .ins()
        .iadd_imm(ptr, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    builder.ins().atomic_rmw(
        types::I64,
        MemFlags::trusted(),
        AtomicRmwOp::Add,
        rc_addr,
        one,
    );
}

/// Emit inline atomic RC increment with nullary tag guard.
///
/// For Mixed HeapCategory types, checks if the value is a bare nullary tag
/// (below NULLARY_TAG_THRESHOLD) before accessing the RC header.
pub(crate) fn emit_rc_inc_guarded(builder: &mut FunctionBuilder, ptr: Value) {
    let cont_block = builder.create_block();
    let inc_block = builder.create_block();

    let threshold = builder.ins().iconst(types::I64, NULLARY_THRESHOLD_I64);
    let is_tag = builder.ins().icmp(IntCC::UnsignedLessThan, ptr, threshold);
    builder
        .ins()
        .brif(is_tag, cont_block, &[], inc_block, &[]);

    builder.switch_to_block(inc_block);
    builder.seal_block(inc_block);

    let rc_addr = builder
        .ins()
        .iadd_imm(ptr, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    builder.ins().atomic_rmw(
        types::I64,
        MemFlags::trusted(),
        AtomicRmwOp::Add,
        rc_addr,
        one,
    );

    builder.ins().jump(cont_block, &[]);
    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}

/// Emit inline atomic RC decrement + conditional dealloc.
///
/// For Mixed HeapCategory types (ADTs with both nullary and data constructors
/// like Option), a null guard checks if the value is a bare tag (below
/// NULLARY_TAG_THRESHOLD) before accessing the RC header.
///
/// old = atomic_rmw(Sub, ptr + RC_OFFSET, 1, Release)
/// if old == 1:
///     fence(Acquire)
///     call drop_glue(ptr)   [if type has heap fields]
///     call runtime/dealloc(ptr)
///
/// The `dealloc_func_id` is the FuncId for `runtime/dealloc`.
/// The `drop_glue_id` is Some(FuncId) if the type has heap-typed fields.
/// If `guard_nullary` is true, emit a check that skips dec for bare tags.
pub(crate) fn emit_rc_dec<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    ptr: Value,
    dealloc_func_id: FuncId,
    drop_glue_id: Option<FuncId>,
) {
    emit_rc_dec_guarded(builder, module, ptr, dealloc_func_id, drop_glue_id, false);
}

/// Emit RC dec with optional null guard for bare nullary tags.
///
/// When `guard_nullary` is true, values below `NULLARY_TAG_THRESHOLD` (bare
/// ADT tags from nullary constructors) are skipped — they are not heap
/// pointers and have no RC header.
pub(crate) fn emit_rc_dec_guarded<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    ptr: Value,
    dealloc_func_id: FuncId,
    drop_glue_id: Option<FuncId>,
    guard_nullary: bool,
) {
    let cont_block = builder.create_block();

    // Guard: if value is a bare nullary tag, skip the dec entirely.
    if guard_nullary {
        let threshold = builder.ins().iconst(types::I64, NULLARY_THRESHOLD_I64);
        let is_tag = builder.ins().icmp(IntCC::UnsignedLessThan, ptr, threshold);
        let dec_block = builder.create_block();
        builder
            .ins()
            .brif(is_tag, cont_block, &[], dec_block, &[]);
        builder.switch_to_block(dec_block);
        builder.seal_block(dec_block);
    }

    let rc_addr = builder
        .ins()
        .iadd_imm(ptr, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    let old_rc = builder.ins().atomic_rmw(
        types::I64,
        MemFlags::trusted(),
        AtomicRmwOp::Sub,
        rc_addr,
        one,
    );

    // Branch: if old_rc == 1 (last reference), free the object.
    let cmp = builder.ins().icmp(IntCC::Equal, old_rc, one);
    let free_block = builder.create_block();

    builder
        .ins()
        .brif(cmp, free_block, &[], cont_block, &[]);

    // Free path: Acquire fence, optional drop glue, then dealloc.
    builder.switch_to_block(free_block);
    builder.seal_block(free_block);
    builder.ins().fence();

    // Call drop glue if this type has heap-typed fields.
    if let Some(glue_id) = drop_glue_id {
        let glue_ref = module.declare_func_in_func(glue_id, builder.func);
        builder.ins().call(glue_ref, &[ptr]);
    }

    // Call runtime/dealloc.
    let dealloc_ref = module.declare_func_in_func(dealloc_func_id, builder.func);
    builder.ins().call(dealloc_ref, &[ptr]);

    builder.ins().jump(cont_block, &[]);

    // Continue path: nothing to do.
    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}

// ---------------------------------------------------------------------------
// Allocation helper
// ---------------------------------------------------------------------------

/// Emit a call to `runtime/alloc` with the given payload size (bytes).
/// Returns the base pointer (i64) to the new allocation (rc=1).
pub(crate) fn emit_alloc<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    alloc_func_id: FuncId,
    payload_size: i64,
) -> Value {
    let size_val = builder.ins().iconst(types::I64, payload_size);
    let alloc_ref = module.declare_func_in_func(alloc_func_id, builder.func);
    let call = builder.ins().call(alloc_ref, &[size_val]);
    builder.inst_results(call)[0]
}

// ---------------------------------------------------------------------------
// ADT helper: determine if a type has mixed nullary + data constructors
// ---------------------------------------------------------------------------

/// Check if a type has mixed nullary and data constructors (for match discrimination).
pub(crate) fn is_mixed_adt<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    fqtn: &FQTypeName,
) -> bool
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    symbol_tables.get(&fqtn.module)
        .map(|table| {
            // The TypeDefInfo lives on a `TypeDef` entry (sum/enum) or, for a
            // single-ctor product type (S79 Option 3a), on the product ctor
            // `Def`'s `type_def` facet — a product is never mixed (one ctor),
            // but resolve uniformly for robustness.
            let type_key = Symbol::from(fqtn.name.as_ref());
            let ctor_names: Vec<Symbol> = match table.get(type_key.as_ref()) {
                Some(ModuleEntry::TypeDef { info, .. }) => info.constructors.clone(),
                Some(ModuleEntry::Def { kind, .. }) => match &**kind {
                    cranelisp_types::DefKind::Constructor { type_def: Some(td), .. } => {
                        td.constructors.clone()
                    }
                    _ => return false,
                },
                _ => return false,
            };
            // Walk each constructor NAME → its DefKind::Constructor Def for the
            // field count (TypeDefInfo.constructors is Vec<Symbol> post-S70).
            let mut has_nullary = false;
            let mut has_data = false;
            for ctor_name in &ctor_names {
                if let Some(fc) = ctor_field_count(table.value(), ctor_name) {
                    if fc == 0 {
                        has_nullary = true;
                    } else {
                        has_data = true;
                    }
                }
            }
            has_nullary && has_data
        })
        .unwrap_or(false)
}

/// Read the field count for a constructor name from its
/// `ModuleEntry::Def { kind: DefKind::Constructor { field_count, .. }, .. }`
/// entry within the given symbol table. Returns `None` if the name is not a
/// constructor in this table.
fn ctor_field_count<C, L>(
    table: &SymbolTable<C, L>,
    ctor_name: &Symbol,
) -> Option<usize>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // S79 Option 3a: product ctors are got-slotted `Def`s exactly like sum
    // ctors (with a `type_def: Some(..)` facet), so the one `Def` arm covers
    // both — its `field_count` is the arity. The prior `TypeDef`-with-
    // `constructor_scheme` product leg is retired.
    match table.get(ctor_name.as_ref()) {
        Some(ModuleEntry::Def { kind, .. }) => match &**kind {
            cranelisp_types::DefKind::Constructor { field_count, .. } => Some(*field_count),
            _ => None,
        },
        _ => None,
    }
}

/// Threshold constant for discriminating nullary tags from heap pointers.
pub const NULLARY_THRESHOLD_I64: i64 = NULLARY_TAG_THRESHOLD as i64;

// ---------------------------------------------------------------------------
// Heap classification — relocated from cranelisp-types per S69 Sub 38
// ---------------------------------------------------------------------------

/// Whether a type requires heap allocation at runtime.
/// Single source of truth for backend codegen.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapCategory {
    /// Never heap-allocated: Int, Bool, Float, nullary constructors
    NeverHeap,
    /// Always heap-allocated: String, closures, data constructors with fields
    AlwaysHeap,
    /// May or may not be heap: polymorphic types, some ADTs with mixed constructors
    Mixed,
}

impl HeapCategory {
    /// Classify a type's heap behavior. Single source of truth.
    ///
    /// Accepts an optional reference to the per-module symbol tables (DashMap)
    /// to make authoritative decisions about ADT heap behavior based on actual
    /// constructor definitions. When `symbol_tables` is `None` (e.g., during
    /// early pipeline stages before type checking), ADTs conservatively classify
    /// as `Mixed`.
    ///
    /// With symbol tables, classification is exact:
    /// - All constructors nullary (no fields) -> `NeverHeap` (bare tags)
    /// - All constructors have fields -> `AlwaysHeap` (always heap-allocated)
    /// - Mix of nullary and data constructors -> `Mixed`
    pub fn classify<C, L>(
        ty: &Type,
        symbol_tables: Option<&dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>>,
    ) -> HeapCategory
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        // S84 Wave 2 — belt-and-braces 0375/0379. The TYPECHECK half (the
        // POSITION-COMPLETE §3.11.1 ambiguity check, `cranelisp-typecheck`
        // `find_ambiguous_value_position`, sharing the
        // `Type::is_representation_undetermined()` predicate) is the LANDED fix:
        // it rejects a genuinely-unpinned representation-undetermined value
        // (`(Option a)` whose var no use pins) UPSTREAM at typecheck with a source
        // location, while correctly ADMITTING a sound polymorphic value whose var
        // is quantified into the enclosing defn's scheme (pinned per-instantiation
        // by monomorphisation).
        //
        // The BACKEND-half panic the §1.6 spec names (`panic iff classify ==
        // Mixed && is_representation_undetermined()`) is **DEFERRED — blocked on
        // FIXME 0374 (full monomorphisation, Wave 1) being TOTAL.** Empirically
        // (S84 Wave 2 /dev) the prelude/stdlib compiles GENERIC-FUNCTION BODIES
        // whose value positions carry sound, scheme-quantified free vars — a bare
        // `Type::Var` (a constructor-arg field) AND a `Mixed`-shaped ADT-with-
        // free-var (`(List a)` in `collections.list`). These are SOUND (the var
        // is pinned per concrete instantiation; the typecheck check correctly
        // admits them), but the backend, lacking scheme context, cannot tell a
        // sound quantified var from an unpinned one — so the panic fires on the
        // valid prelude (the §1.6 "premature landing" risk made concrete; BC
        // ring2-rc §1.6 Risk). The non-crashing `Mixed` fallback is the
        // operatively load-bearing safety net only TOTAL concreteness retires.
        //
        // FIXME 0381 (`target: /typecheck`) records the 0374 gap (generic bodies
        // are still compiled, not rendered slot-less/uncompiled). When 0374 is
        // total — no free var in any COMPILED body — re-arm the backstop by
        // restoring the gated `panic!` here:
        //   if category == HeapCategory::Mixed && ty.is_representation_undetermined()
        //       { panic!(... BC §3 invariant 9 ...) }
        // and restore the `should_panic` `test_var_panics` /
        // `test_mixed_adt_with_free_var_panics` unit tests. The 4 §3.11.1
        // acceptance guards flip GREEN on the TYPECHECK half alone (they are
        // rejected before codegen), so the deferral does not weaken them.
        match ty {
            Type::Int | Type::Bool | Type::Float => HeapCategory::NeverHeap,
            Type::String => HeapCategory::AlwaysHeap,
            Type::Fn(_, _) => {
                // In Ring 0, functions are bare pointers (NeverHeap).
                // In Ring 1+, closures are heap-allocated.
                // Conservative: AlwaysHeap (closures are the common case after Ring 0).
                HeapCategory::AlwaysHeap
            }
            Type::ADT(fqtn, _) => Self::classify_adt(fqtn, symbol_tables),
            Type::Var(_) | Type::TyConApp(_, _) => {
                // Unresolved type variable / partially-applied HKT head: no static
                // representation knowledge. Conservative `Mixed` fallback (the
                // backstop panic is DEFERRED on FIXME 0374/0381 — see above).
                HeapCategory::Mixed
            }
        }
    }

    /// Classify an ADT by inspecting its constructors from the symbol tables.
    ///
    /// Without the symbol tables, conservatively returns `Mixed`.
    /// With the symbol tables, looks up `ModuleEntry::TypeDef` on the type's
    /// owning module and counts nullary vs data constructors:
    /// - All nullary -> `NeverHeap`
    /// - All data -> `AlwaysHeap`
    /// - Mixed -> `Mixed`
    fn classify_adt<C, L>(
        fqtn: &FQTypeName,
        symbol_tables: Option<&dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>>,
    ) -> HeapCategory
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        // Vec is a built-in heap type (not registered via deftype).
        if fqtn.name.as_ref() == "Vec" {
            return HeapCategory::AlwaysHeap;
        }

        let Some(tables) = symbol_tables else {
            // No tables available — conservative fallback
            return HeapCategory::Mixed;
        };

        // Look up the TypeDefInfo on the type's owning module.
        let Some(table) = tables.get(&fqtn.module) else {
            return HeapCategory::Mixed;
        };

        // The TypeDefInfo (which names the type's constructors) lives on a
        // `TypeDef` entry (sum/enum) or, for a single-ctor **product** type
        // (S79 Option 3a), on the got-slotted product ctor `Def`'s
        // `DefKind::Constructor { type_def: Some(..) }` type facet — the
        // product `type_name` key IS the ctor `Def`, not a `TypeDef`.
        let type_key = Symbol::from(fqtn.name.as_ref());
        let ctor_names: Vec<Symbol> = match table.get(type_key.as_ref()) {
            Some(ModuleEntry::TypeDef { info, .. }) => info.constructors.clone(),
            Some(ModuleEntry::Def { kind, .. }) => match &**kind {
                cranelisp_types::DefKind::Constructor { type_def: Some(td), .. } => {
                    td.constructors.clone()
                }
                _ => return HeapCategory::Mixed,
            },
            _ => return HeapCategory::Mixed,
        };

        Self::classify_from_ctor_names(table.value(), &ctor_names)
    }

    /// Classify an ADT from its constructor NAMES (ctor-as-Def shape, S70).
    ///
    /// `TypeDefInfo.constructors` is `Vec<Symbol>` (names only); the
    /// per-constructor field count lives on each ctor's `ModuleEntry::Def` at
    /// `kind: DefKind::Constructor { field_count, .. }`. This walks each name
    /// through the symbol table to count nullary (field_count == 0) vs data
    /// (field_count > 0) constructors:
    /// - All nullary -> `NeverHeap` (bare tags)
    /// - All data -> `AlwaysHeap`
    /// - Mix -> `Mixed`
    /// - No resolvable constructors -> `Mixed` (conservative).
    fn classify_from_ctor_names<C, L>(
        table: &SymbolTable<C, L>,
        ctor_names: &[Symbol],
    ) -> HeapCategory
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        let mut has_nullary = false;
        let mut has_data = false;
        let mut resolved_any = false;
        for ctor_name in ctor_names {
            if let Some(fc) = ctor_field_count(table, ctor_name) {
                resolved_any = true;
                if fc == 0 {
                    has_nullary = true;
                } else {
                    has_data = true;
                }
            }
        }
        if !resolved_any {
            return HeapCategory::Mixed;
        }
        match (has_nullary, has_data) {
            (true, false) => HeapCategory::NeverHeap,
            (false, true) => HeapCategory::AlwaysHeap,
            _ => HeapCategory::Mixed,
        }
    }
}

// Heap classifier tests — rebuilt against the ctor-as-Def shape (S70). The
// retired `ConstructorInfo` struct is replaced by `ModuleEntry::Def { kind:
// DefKind::Constructor { type_name, tag, field_count, .. }, .. }` entries per
// constructor name; `TypeDefInfo.constructors` is `Vec<Symbol>` (names only).
// The classifier walks each name → its Def for the field count. See
// `design/backend/compile-to-module.md` §2.6 + `DefKind::Constructor` rustdoc.
#[cfg(test)]
mod heap_category_tests {
    use super::*;
    use cranelisp_types::{DefKind, FQTypeName, Scheme, TypeDefInfo, TypeName, Visibility};

    const TEST_MOD: &str = "test";

    /// A constructor spec for test fixtures: name, tag, and field count.
    struct CtorSpec {
        name: &'static str,
        tag: usize,
        field_count: usize,
    }

    /// Test helper: create an FQTypeName in a "test" module.
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from(TEST_MOD), TypeName::from(name))
    }

    /// Helper: nullary constructor spec (no fields).
    fn nullary_ctor(name: &'static str, tag: usize) -> CtorSpec {
        CtorSpec { name, tag, field_count: 0 }
    }

    /// Helper: data constructor spec with the given field count.
    fn data_ctor(name: &'static str, tag: usize, field_count: usize) -> CtorSpec {
        CtorSpec { name, tag, field_count }
    }

    /// Build a constructor `Def` entry under the ctor-as-Def shape.
    /// `type_def` is `Some(..)` for a single-ctor product type (the ctor IS
    /// its own type — S79 Option 3a dual facet), `None` for sum/enum ctors.
    fn ctor_def_entry(
        type_fqtn: &FQTypeName,
        spec: &CtorSpec,
        type_def: Option<Box<TypeDefInfo>>,
    ) -> ModuleEntry {
        let scheme = Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: Type::ADT(type_fqtn.clone(), vec![]),
        };
        ModuleEntry::Def {
            scheme,
            visibility: Visibility::Public,
            docstring: None,
            param_names: (0..spec.field_count)
                .map(|i| Symbol::from(format!("f{i}")))
                .collect(),
            kind: Box::new(DefKind::Constructor {
                got_slot: 0,
                type_name: type_fqtn.clone(),
                tag: spec.tag,
                field_count: spec.field_count,
                internal: false,
                type_def,
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            code: None,
        }
    }

    /// Build a DashMap with a single module, mirroring the production
    /// registration shape (S79 Option 3a, `cranelisp-typecheck::adt`):
    /// every constructor — sum, enum, OR product — is a got-slotted
    /// `ModuleEntry::Def { kind: DefKind::Constructor { .. }, .. }`. For a
    /// **product type** (single constructor whose name equals the type name)
    /// that `Def` ALSO carries the type facet `type_def: Some(TypeDefInfo)`
    /// and IS the `type_name` key — there is no separate `TypeDef` entry, and
    /// the prior `constructor_scheme`-smuggling `TypeDef` is retired. For
    /// sum/enum types each ctor `Def` is keyed distinctly and a separate
    /// `ModuleEntry::TypeDef` is inserted under the type name.
    fn tables_with_type(
        type_name: &str,
        type_params: &[&str],
        ctors: &[CtorSpec],
    ) -> dashmap::DashMap<ModuleFullPath, SymbolTable> {
        let tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
        let mut st = SymbolTable::new(ModuleFullPath::from(TEST_MOD));
        let fqtn = test_fqtn(type_name);

        let info = TypeDefInfo {
            name: fqtn.clone(),
            type_params: type_params.iter().map(|s| Symbol::from(*s)).collect(),
            constructors: ctors.iter().map(|c| Symbol::from(c.name)).collect(),
        };

        let is_product = ctors.len() == 1 && ctors[0].name == type_name;

        // Insert ctor Defs. The product ctor carries its type facet and IS the
        // type-name key; sum/enum ctors carry `type_def: None`.
        for spec in ctors {
            let type_def = if is_product {
                Some(Box::new(info.clone()))
            } else {
                None
            };
            st.insert(
                Symbol::from(spec.name),
                ctor_def_entry(&fqtn, spec, type_def),
            );
        }

        // Sum/enum: a separate `TypeDef` entry under the type name. A product
        // type needs NONE — its got-slotted ctor `Def` already answers as the
        // type via its `type_def` facet.
        if !is_product {
            st.insert(
                Symbol::from(type_name),
                ModuleEntry::TypeDef {
                    info,
                    visibility: Visibility::Public,
                    docstring: None,
                },
            );
        }
        tables.insert(ModuleFullPath::from(TEST_MOD), st);
        tables
    }

    // --- Primitive types (no tables needed) ---

    #[test]
    fn test_primitives_never_heap() {
        assert_eq!(
            HeapCategory::classify::<(), ()>(&Type::Int, None),
            HeapCategory::NeverHeap
        );
        assert_eq!(
            HeapCategory::classify::<(), ()>(&Type::Bool, None),
            HeapCategory::NeverHeap
        );
        assert_eq!(
            HeapCategory::classify::<(), ()>(&Type::Float, None),
            HeapCategory::NeverHeap
        );
    }

    #[test]
    fn test_string_always_heap() {
        assert_eq!(
            HeapCategory::classify::<(), ()>(&Type::String, None),
            HeapCategory::AlwaysHeap
        );
    }

    #[test]
    fn test_fn_always_heap() {
        let fn_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        assert_eq!(
            HeapCategory::classify::<(), ()>(&fn_ty, None),
            HeapCategory::AlwaysHeap
        );
    }

    // S84 Wave 2 — belt-and-braces 0375/0379. The TYPECHECK half (the
    // position-complete §3.11.1 check) is the landed fix; the BACKEND-half panic
    // is DEFERRED on FIXME 0374/0381 (the prelude/stdlib compiles GENERIC BODIES
    // whose value positions carry sound scheme-quantified free vars — bare
    // `Type::Var` AND `Mixed`-ADT-with-free-var like `(List a)` — which the
    // backend, lacking scheme context, cannot distinguish from unpinned ones).
    // So a bare `Type::Var` / `TyConApp` keeps its conservative `Mixed` fallback,
    // NOT a panic. These tests pin the DEFERRED state and document the re-arm
    // target (see `HeapCategory::classify` for the gated `panic!` to restore once
    // 0374 is total).
    #[test]
    fn test_var_is_mixed_fallback_backstop_deferred() {
        // Re-arm target (FIXME 0381): this becomes #[should_panic] once 0374 is
        // total (no free var in any compiled body).
        assert_eq!(
            HeapCategory::classify::<(), ()>(&Type::Var(0), None),
            HeapCategory::Mixed,
        );
    }

    #[test]
    fn test_tyconapp_is_mixed_fallback_backstop_deferred() {
        assert_eq!(
            HeapCategory::classify::<(), ()>(&Type::TyConApp(0, vec![Type::Int]), None),
            HeapCategory::Mixed,
        );
    }

    // The `Mixed`-shaped ADT CARRYING A FREE VAR (the `(Option a)` / `(Box a)` /
    // `(List a)` family) — the 0379 hole at the backend seam — likewise keeps the
    // `Mixed` fallback while the backstop is deferred (FIXME 0381: the prelude
    // compiles such values in sound generic bodies). The TYPECHECK position-
    // complete §3.11.1 check is what rejects a GENUINELY-unpinned `(Option a)`
    // (free-at-root) upstream; this backend seam classifies the sound
    // scheme-quantified ones `Mixed` without crashing. Re-arm target (FIXME 0381):
    // this becomes #[should_panic] once 0374 is total.
    #[test]
    fn test_mixed_adt_with_free_var_is_mixed_backstop_deferred() {
        // (deftype (Option a) None (Some [:a val])) — Mixed ctor shape …
        let tables = tables_with_type(
            "Option",
            &["a"],
            &[nullary_ctor("None", 0), data_ctor("Some", 1, 1)],
        );
        // … carrying a FREE var in its args (unpinned `a`).
        let option_var = Type::ADT(test_fqtn("Option"), vec![Type::Var(0)]);
        assert_eq!(
            HeapCategory::classify(&option_var, Some(&tables)),
            HeapCategory::Mixed,
        );
    }

    // --- ADT without tables (conservative fallback) ---

    #[test]
    fn test_adt_without_tables_is_mixed() {
        let color = Type::ADT(test_fqtn("Color"), vec![]);
        assert_eq!(
            HeapCategory::classify::<(), ()>(&color, None),
            HeapCategory::Mixed,
        );
    }

    #[test]
    fn test_parameterized_adt_without_tables_is_mixed() {
        let option_int = Type::ADT(test_fqtn("Option"), vec![Type::Int]);
        assert_eq!(
            HeapCategory::classify::<(), ()>(&option_int, None),
            HeapCategory::Mixed,
        );
    }

    // --- ADT with tables: enum-only (all nullary) ---

    #[test]
    fn test_enum_only_adt_never_heap() {
        // (deftype Color Red Green Blue)
        let tables = tables_with_type(
            "Color",
            &[],
            &[
                nullary_ctor("Red", 0),
                nullary_ctor("Green", 1),
                nullary_ctor("Blue", 2),
            ],
        );
        let color = Type::ADT(test_fqtn("Color"), vec![]);
        assert_eq!(
            HeapCategory::classify(&color, Some(&tables)),
            HeapCategory::NeverHeap,
        );
    }

    // --- ADT with tables: all data constructors ---

    #[test]
    fn test_data_only_adt_always_heap() {
        // (deftype Wrapper [val]) — non-parameterized with data constructor
        // This is the F-2 bug case: was incorrectly NeverHeap
        let tables = tables_with_type(
            "Wrapper",
            &[],
            &[data_ctor("Wrapper", 0, 1)],
        );
        let wrapper = Type::ADT(test_fqtn("Wrapper"), vec![]);
        assert_eq!(
            HeapCategory::classify(&wrapper, Some(&tables)),
            HeapCategory::AlwaysHeap,
        );
    }

    #[test]
    fn test_product_type_always_heap() {
        // (deftype IPoint (IPoint [:Int x :Int y])) — product type
        let tables = tables_with_type(
            "IPoint",
            &[],
            &[data_ctor("IPoint", 0, 2)],
        );
        let point = Type::ADT(test_fqtn("IPoint"), vec![]);
        assert_eq!(
            HeapCategory::classify(&point, Some(&tables)),
            HeapCategory::AlwaysHeap,
        );
    }

    // --- ADT with tables: mixed constructors ---

    // regression: KEPT path (FIXME 0375/0379). A type-KNOWN `Mixed` ADT with NO
    // free var (`is_representation_undetermined()` is FALSE) still classifies as
    // `Mixed` and keeps its sound `<1024` nullary-tag discrimination guard — it
    // must NOT be swept into the widened panic. This is the `(true,true)` ctor
    // shape → `Mixed` → `emit_rc_*_guarded` chain that must stay intact.
    #[test]
    fn test_mixed_adt_with_tables() {
        // (deftype (Option a) None (Some [:a val]))
        let tables = tables_with_type(
            "Option",
            &["a"],
            &[nullary_ctor("None", 0), data_ctor("Some", 1, 1)],
        );
        let option_int = Type::ADT(test_fqtn("Option"), vec![Type::Int]);
        assert_eq!(
            HeapCategory::classify(&option_int, Some(&tables)),
            HeapCategory::Mixed,
        );
    }

    // --- ADT with tables: parameterized but only nullary ---

    #[test]
    fn test_phantom_type_never_heap() {
        // (deftype (Phantom a) PhantomVal) — parameterized, but only nullary constructor
        // This was incorrectly Mixed with the old heuristic
        let tables = tables_with_type(
            "Phantom",
            &["a"],
            &[nullary_ctor("PhantomVal", 0)],
        );
        let phantom = Type::ADT(test_fqtn("Phantom"), vec![Type::Int]);
        assert_eq!(
            HeapCategory::classify(&phantom, Some(&tables)),
            HeapCategory::NeverHeap,
        );
    }

    // --- ADT with tables: unknown type (not in tables) ---

    #[test]
    fn test_unknown_adt_with_empty_tables_is_mixed() {
        let tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
        let unknown = Type::ADT(test_fqtn("Unknown"), vec![]);
        assert_eq!(
            HeapCategory::classify(&unknown, Some(&tables)),
            HeapCategory::Mixed,
        );
    }

    // --- Vec type (built-in, always heap) ---

    #[test]
    fn test_vec_always_heap_without_tables() {
        let vec_int = Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
            vec![Type::Int],
        );
        assert_eq!(
            HeapCategory::classify::<(), ()>(&vec_int, None),
            HeapCategory::AlwaysHeap,
        );
    }

    #[test]
    fn test_vec_always_heap_with_tables() {
        let tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
        let vec_str = Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
            vec![Type::String],
        );
        assert_eq!(
            HeapCategory::classify(&vec_str, Some(&tables)),
            HeapCategory::AlwaysHeap,
        );
    }

    #[test]
    fn test_vec_polymorphic_always_heap() {
        let vec_var = Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
            vec![Type::Var(0)],
        );
        assert_eq!(
            HeapCategory::classify::<(), ()>(&vec_var, None),
            HeapCategory::AlwaysHeap,
        );
    }
}

// ---------------------------------------------------------------------------
// Last-use analysis
// ---------------------------------------------------------------------------

/// Compute last-use information for all variables in an expression.
///
/// Returns a map from (variable_name, use_span) -> is_last_use.
/// A variable's "last use" is the final textual reference to it within its scope.
///
/// Ring 1 simplified approach: walk the expression tree and for each variable,
/// record all use sites. The last one in a pre-order traversal is the last use.
pub(crate) fn compute_last_uses(
    expr: &cranelisp_types::Expr,
) -> HashMap<(cranelisp_types::Symbol, cranelisp_types::Span), bool> {
    use cranelisp_types::{Symbol, Span};

    let mut uses: HashMap<Symbol, Vec<Span>> = HashMap::new();
    collect_var_uses(expr, &mut uses);

    let mut result = HashMap::new();
    for (name, spans) in &uses {
        for (i, span) in spans.iter().enumerate() {
            let is_last = i == spans.len() - 1;
            result.insert((name.clone(), *span), is_last);
        }
    }
    result
}

/// Collect all variable references in pre-order traversal.
fn collect_var_uses(
    expr: &cranelisp_types::Expr,
    uses: &mut HashMap<cranelisp_types::Symbol, Vec<cranelisp_types::Span>>,
) {
    use cranelisp_types::Expr;

    match expr {
        Expr::Var { name, span, .. } => {
            uses.entry(name.clone()).or_default().push(*span);
        }
        Expr::Let { bindings, body, .. } => {
            for (_, val) in bindings {
                collect_var_uses(val, uses);
            }
            collect_var_uses(body, uses);
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            collect_var_uses(cond, uses);
            collect_var_uses(then_branch, uses);
            collect_var_uses(else_branch, uses);
        }
        Expr::Lambda { body, .. } => {
            collect_var_uses(body, uses);
        }
        Expr::Apply { callee, args, .. } => {
            collect_var_uses(callee, uses);
            for arg in args {
                collect_var_uses(arg, uses);
            }
        }
        Expr::Match { scrutinee, arms, .. } => {
            collect_var_uses(scrutinee, uses);
            for arm in arms {
                collect_var_uses(&arm.body, uses);
            }
        }
        Expr::Annotate { expr, .. } => {
            collect_var_uses(expr, uses);
        }
        Expr::VecLit { elements, .. } => {
            for e in elements {
                collect_var_uses(e, uses);
            }
        }
        Expr::Trace { body, .. } => {
            collect_var_uses(body, uses);
        }
        Expr::ParBind { bindings, body, .. } => {
            for (_, val_expr) in bindings {
                collect_var_uses(val_expr, uses);
            }
            collect_var_uses(body, uses);
        }
        Expr::ConstrADT { fields, .. } => {
            for f in fields {
                collect_var_uses(f, uses);
            }
        }
        // Literals have no variable references.
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: 12-runtime §12.1.4 — ADT heap layout offsets (tag at 16, fields at 24+)
    #[test]
    fn test_heap_adt_layout() {
        assert_eq!(HeapAdt::TAG_OFFSET, 16);
        assert_eq!(HeapAdt::FIELDS_START, 24);
        assert_eq!(HeapAdt::field_offset(0), 24);
        assert_eq!(HeapAdt::field_offset(1), 32);
        assert_eq!(HeapAdt::payload_size(0), 8); // tag only
        assert_eq!(HeapAdt::payload_size(2), 24); // tag + 2 fields
    }

    // spec: 12-runtime §12.1.3 — closure heap layout (code_ptr at 16, drop_glue at 24, captures at 32+)
    #[test]
    fn test_heap_closure_layout() {
        assert_eq!(HeapClosure::CODE_PTR_OFFSET, 16);
        assert_eq!(HeapClosure::DROP_GLUE_PTR_OFFSET, 24);
        assert_eq!(HeapClosure::CAPTURES_START, 32);
        assert_eq!(HeapClosure::capture_offset(0), 32);
        assert_eq!(HeapClosure::capture_offset(1), 40);
        assert_eq!(HeapClosure::payload_size(0), 16); // code_ptr + drop_glue_ptr only
        assert_eq!(HeapClosure::payload_size(3), 40); // code_ptr + drop_glue_ptr + 3 captures
    }

    // spec: 12-runtime §12.1.5 — Vec heap layout (len/cap/data_ptr at 16/24/32)
    #[test]
    fn test_heap_vec_layout() {
        assert_eq!(HeapVec::LEN_OFFSET, 16);
        assert_eq!(HeapVec::CAP_OFFSET, 24);
        assert_eq!(HeapVec::DATA_PTR_OFFSET, 32);
        assert_eq!(HeapVec::payload_size(), 24);
        assert_eq!(std::mem::size_of::<HeapVec>(), 40);
    }

    // spec: 12-runtime §12.3 — last-use analysis for RC consuming calling convention
    #[test]
    fn test_compute_last_uses() {
        use cranelisp_types::{Expr, Span, Symbol};

        let x = Symbol::from("x");
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var { name: Symbol::from("f"), span: Span::new(0, 1), resolved_call: None, inferred_type: None }),
            args: vec![
                Expr::Var { name: x.clone(), span: Span::new(2, 3), resolved_call: None, inferred_type: None },
                Expr::Var { name: x.clone(), span: Span::new(4, 5), resolved_call: None, inferred_type: None },
            ],
            span: Span::new(0, 6),
            resolved_call: None,
            inferred_type: None,
        };

        let last_uses = compute_last_uses(&expr);
        // First use of x is NOT last use.
        assert_eq!(last_uses.get(&(x.clone(), Span::new(2, 3))), Some(&false));
        // Second use of x IS last use.
        assert_eq!(last_uses.get(&(x.clone(), Span::new(4, 5))), Some(&true));
    }
}
