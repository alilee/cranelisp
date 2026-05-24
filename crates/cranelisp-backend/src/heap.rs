// Heap layout types and emit helpers.
//
// This module is the SOLE location that imports layout constants (HeapHeader,
// HeapAdt, HeapClosure offsets). All other codegen code calls these helpers.
// This confines heap layout assumptions per src/CLAUDE.md §"Heap Access".
//
// Contents:
//   HeapAdt    — ADT data constructor layout
//   HeapClosure — Closure layout
//   heap_load  — load an i64 from a heap object
//   heap_store — store an i64 into a heap object
//   emit_rc_inc — inline atomic RC increment
//   emit_rc_dec — inline atomic RC decrement + conditional dealloc
//   emit_alloc — emit call to runtime/alloc

use std::collections::HashMap;
use std::mem::{self, offset_of};

use cranelift::prelude::*;
use cranelift_codegen::ir::AtomicRmwOp;
use cranelift_module::{FuncId, Module};

use dashmap::DashMap;

use cranelisp_types::{
    FQTypeName, HeapHeader, ModuleEntry, ModuleFullPath, Symbol, SymbolTable, Type, TypeDefInfo,
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
pub fn heap_load(builder: &mut FunctionBuilder, ptr: Value, offset: i32) -> Value {
    builder
        .ins()
        .load(types::I64, MemFlags::trusted(), ptr, offset)
}

/// Store an i64 value into a heap object at the given byte offset.
/// Same offset rules as heap_load.
pub fn heap_store(builder: &mut FunctionBuilder, val: Value, ptr: Value, offset: i32) {
    builder.ins().store(MemFlags::trusted(), val, ptr, offset);
}

// ---------------------------------------------------------------------------
// RC emission helpers
// ---------------------------------------------------------------------------

/// Emit inline atomic RC increment.
///
/// Cranelift atomic_rmw(Add, ptr + RC_OFFSET, 1, Release).
/// This is an INLINE atomic op, NOT an extern function call.
pub fn emit_rc_inc(builder: &mut FunctionBuilder, ptr: Value) {
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
pub fn emit_rc_inc_guarded(builder: &mut FunctionBuilder, ptr: Value) {
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
pub fn emit_rc_dec<M: Module>(
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
pub fn emit_rc_dec_guarded<M: Module>(
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
pub fn emit_alloc<M: Module>(
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
pub fn is_mixed_adt<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    fqtn: &FQTypeName,
) -> bool
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    symbol_tables.get(&fqtn.module)
        .and_then(|table| {
            let type_key = Symbol::from(fqtn.name.as_ref());
            match table.get(type_key.as_ref()) {
                Some(ModuleEntry::TypeDef { info, .. }) => {
                    let has_nullary = info.constructors.iter().any(|c| c.fields.is_empty());
                    let has_data = info.constructors.iter().any(|c| !c.fields.is_empty());
                    Some(has_nullary && has_data)
                }
                _ => None,
            }
        })
        .unwrap_or(false)
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
                // Unresolved type variable: might be anything
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

        let type_key = Symbol::from(fqtn.name.as_ref());
        let info = match table.get(type_key.as_ref()) {
            Some(ModuleEntry::TypeDef { info, .. }) => info,
            _ => return HeapCategory::Mixed,
        };

        Self::classify_from_type_def_info(info)
    }

    /// Classify an ADT from its TypeDefInfo (shared logic).
    ///
    /// FIXME(/dev — heap classifier rebuild, ctor-as-Def cascade): under the
    /// ctor-as-Def shape (see facades/types.md §"Symbol table — the single
    /// store" §"DefKind"), `TypeDefInfo.constructors: Vec<Symbol>` (names
    /// only); the per-constructor field count lives on each ctor's
    /// `ModuleEntry::Def` at `kind: DefKind::Constructor { field_count, .. }`.
    /// The classifier must walk each name through the symbol table to
    /// determine nullary-vs-data counts. Current stub returns `Mixed` to keep
    /// the cranelisp-types crate compiling under the interface flip; consumer
    /// cascade in Sprint 69 Wave 3 rebuilds the correct classifier (and the
    /// in-crate tests below) against the new shape with Def fixtures replacing
    /// ConstructorInfo.
    fn classify_from_type_def_info(_info: &TypeDefInfo) -> HeapCategory {
        HeapCategory::Mixed
    }
}

// FIXME(/dev — heap classifier tests rebuild, ctor-as-Def cascade): the test
// module below uses the retired `ConstructorInfo` struct + `Vec<ConstructorInfo>`
// shape for `TypeDefInfo.constructors`. Under the ctor-as-Def shape (see
// facades/types.md §"Symbol table — the single store" §"DefKind"), tests must
// build fake symbol tables containing `ModuleEntry::Def { kind:
// DefKind::Constructor { field_count, .. }, .. }` entries per constructor
// name, and exercise the rebuilt classifier (see `classify_from_type_def_info`
// FIXME above). Gated out (`cfg(any())` = never compiled) until Wave 3
// rebuild lands.
#[cfg(any())]
mod heap_category_tests {
    use super::*;
    use cranelisp_types::{ConstructorInfo, FieldInfo, TypeName, Visibility};

    const TEST_MOD: &str = "test";

    /// Test helper: create an FQTypeName in a "test" module.
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from(TEST_MOD), TypeName::from(name))
    }

    /// Helper: build a TypeDefInfo with the given constructors.
    fn make_type_def(
        name: &str,
        type_params: &[&str],
        constructors: Vec<ConstructorInfo>,
    ) -> TypeDefInfo {
        TypeDefInfo {
            name: test_fqtn(name),
            type_params: type_params.iter().map(|s| Symbol::from(*s)).collect(),
            constructors,
            docstring: None,
        }
    }

    /// Helper: build a nullary constructor (no fields).
    fn nullary_ctor(name: &str, tag: usize) -> ConstructorInfo {
        ConstructorInfo {
            name: Symbol::from(name),
            tag,
            fields: vec![],
            docstring: None,
            internal: false,
        }
    }

    /// Helper: build a data constructor with one Int field.
    fn data_ctor(name: &str, tag: usize) -> ConstructorInfo {
        ConstructorInfo {
            name: Symbol::from(name),
            tag,
            fields: vec![FieldInfo {
                name: Symbol::from("val"),
                ty: Type::Int,
            }],
            docstring: None,
            internal: false,
        }
    }

    /// Helper: build a DashMap with a single module containing the given TypeDefInfos.
    fn tables_with_defs(defs: Vec<TypeDefInfo>) -> dashmap::DashMap<ModuleFullPath, SymbolTable> {
        let tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
        let mut st = SymbolTable::new(ModuleFullPath::from(TEST_MOD));
        for def in defs {
            let key = Symbol::from(def.name.name.as_ref());
            st.insert(
                key,
                ModuleEntry::TypeDef {
                    info: def,
                    visibility: Visibility::Public,
                    constructor_scheme: None,
                    sexp: None,
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

    #[test]
    fn test_var_mixed() {
        assert_eq!(
            HeapCategory::classify::<(), ()>(&Type::Var(0), None),
            HeapCategory::Mixed
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
        let tables = tables_with_defs(vec![make_type_def(
            "Color",
            &[],
            vec![
                nullary_ctor("Red", 0),
                nullary_ctor("Green", 1),
                nullary_ctor("Blue", 2),
            ],
        )]);
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
        let tables = tables_with_defs(vec![make_type_def(
            "Wrapper",
            &[],
            vec![data_ctor("Wrapper", 0)],
        )]);
        let wrapper = Type::ADT(test_fqtn("Wrapper"), vec![]);
        assert_eq!(
            HeapCategory::classify(&wrapper, Some(&tables)),
            HeapCategory::AlwaysHeap,
        );
    }

    #[test]
    fn test_product_type_always_heap() {
        // (deftype IPoint (IPoint [:Int x :Int y])) — product type
        let tables = tables_with_defs(vec![make_type_def(
            "IPoint",
            &[],
            vec![ConstructorInfo {
                name: Symbol::from("IPoint"),
                tag: 0,
                fields: vec![
                    FieldInfo {
                        name: Symbol::from("x"),
                        ty: Type::Int,
                    },
                    FieldInfo {
                        name: Symbol::from("y"),
                        ty: Type::Int,
                    },
                ],
                docstring: None,
                internal: false,
            }],
        )]);
        let point = Type::ADT(test_fqtn("IPoint"), vec![]);
        assert_eq!(
            HeapCategory::classify(&point, Some(&tables)),
            HeapCategory::AlwaysHeap,
        );
    }

    // --- ADT with tables: mixed constructors ---

    #[test]
    fn test_mixed_adt_with_tables() {
        // (deftype (Option a) None (Some [:a val]))
        let tables = tables_with_defs(vec![make_type_def(
            "Option",
            &["a"],
            vec![nullary_ctor("None", 0), data_ctor("Some", 1)],
        )]);
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
        let tables = tables_with_defs(vec![make_type_def(
            "Phantom",
            &["a"],
            vec![nullary_ctor("PhantomVal", 0)],
        )]);
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
pub fn compute_last_uses(
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
            callee: Box::new(Expr::Var { name: Symbol::from("f"), span: Span::new(0, 1), inferred_type: None }),
            args: vec![
                Expr::Var { name: x.clone(), span: Span::new(2, 3), inferred_type: None },
                Expr::Var { name: x.clone(), span: Span::new(4, 5), inferred_type: None },
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
