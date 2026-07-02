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
    ConcreteType, FQTypeName, HeapHeader, ModuleEntry, ModuleFullPath, Symbol, SymbolTable,
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
///
/// `module` is threaded for the S99 instrumentation gate (an emitted
/// `runtime/rc_stat_inc` call) and is otherwise unused; with both S99 gates off
/// the emission is byte-identical to the pre-S99 `atomic_rmw` path.
pub(crate) fn emit_rc_inc<M: Module>(builder: &mut FunctionBuilder, module: &mut M, ptr: Value) {
    if rc_stats_codegen_enabled() {
        emit_rc_stat_call(builder, module, "runtime/rc_stat_inc");
    }
    let rc_addr = builder
        .ins()
        .iadd_imm(ptr, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    if nonatomic_rc_codegen_enabled() {
        // S99 measurement-only NON-ATOMIC inc — UNSOUND above one worker.
        let cur = builder.ins().load(types::I64, MemFlags::trusted(), rc_addr, 0);
        let new = builder.ins().iadd(cur, one);
        builder.ins().store(MemFlags::trusted(), new, rc_addr, 0);
    } else {
        builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Add,
            rc_addr,
            one,
        );
    }
}

/// Emit inline atomic RC increment with nullary tag guard.
///
/// For Mixed HeapCategory types, checks if the value is a bare nullary tag
/// (below NULLARY_TAG_THRESHOLD) before accessing the RC header.
pub(crate) fn emit_rc_inc_guarded<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    ptr: Value,
) {
    let cont_block = builder.create_block();
    let inc_block = builder.create_block();

    let threshold = builder.ins().iconst(types::I64, NULLARY_THRESHOLD_I64);
    let is_tag = builder.ins().icmp(IntCC::UnsignedLessThan, ptr, threshold);
    builder
        .ins()
        .brif(is_tag, cont_block, &[], inc_block, &[]);

    builder.switch_to_block(inc_block);
    builder.seal_block(inc_block);

    // S99 stats: count only a real inc (bare nullary tags took the skip branch).
    if rc_stats_codegen_enabled() {
        emit_rc_stat_call(builder, module, "runtime/rc_stat_inc");
    }
    let rc_addr = builder
        .ins()
        .iadd_imm(ptr, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    if nonatomic_rc_codegen_enabled() {
        // S99 measurement-only NON-ATOMIC inc — UNSOUND above one worker.
        let cur = builder.ins().load(types::I64, MemFlags::trusted(), rc_addr, 0);
        let new = builder.ins().iadd(cur, one);
        builder.ins().store(MemFlags::trusted(), new, rc_addr, 0);
    } else {
        builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Add,
            rc_addr,
            one,
        );
    }

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
/// FIXME 0494 localization gate (codegen-time, read once). When
/// `CRANELISP_RC_DEC_CHECK` is set, [`emit_rc_dec_guarded`] emits a
/// `runtime/rc_dec_check(ptr)` call before each inline dec. Off by default.
fn rc_dec_check_enabled() -> bool {
    static E: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *E.get_or_init(|| std::env::var_os("CRANELISP_RC_DEC_CHECK").is_some())
}

/// S99 Wave 0 (arch Phase-2 ruling R4). Codegen-time gate for the NON-ATOMIC RC
/// measurement build. When `CRANELISP_NONATOMIC_RC` is set, the inline RC inc/dec
/// helpers emit a plain load-modify-store (`iadd`/`isub`) instead of an
/// `atomic_rmw`. **This build is UNSOUND above one worker** — a lost-update race
/// on the shared count corrupts the RC (use-after-free / leak). It exists ONLY to
/// isolate the atomic-*instruction* cost at a single-worker spark pool
/// (`RAYON_NUM_THREADS=1`, lenient still ON). Off by default ⇒ the exact
/// `atomic_rmw` path as before (byte-identical-off). It is **excluded from the
/// canonical `cargo nextest run`** and must NEVER ship. The intrinsic-side dec/inc
/// paths (`cranelisp-intrinsics::rc`/`::drop`) read the same env so a whole run is
/// consistently non-atomic.
fn nonatomic_rc_codegen_enabled() -> bool {
    static E: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *E.get_or_init(|| std::env::var_os("CRANELISP_NONATOMIC_RC").is_some())
}

/// S99 Wave 0. Codegen-time gate for RC-op instrumentation. When
/// `CRANELISP_RC_STATS` is set, each inline RC inc/dec emits a call to the
/// `runtime/rc_stat_inc` / `runtime/rc_stat_dec` catalog helper, which tallies the
/// op (printed with the alloc counts at process exit — see `cranelisp-intrinsics::
/// rc`). Off by default ⇒ no call emitted ⇒ byte-identical codegen.
fn rc_stats_codegen_enabled() -> bool {
    static E: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *E.get_or_init(|| std::env::var_os("CRANELISP_RC_STATS").is_some())
}

/// Emit a call to a zero-arg `runtime/rc_stat_*` tally helper (S99 stats gate).
/// Resolved by symbol name (`Linkage::Import`) against the intrinsics catalog, so
/// it is mode-safe (JIT + object/link) and adds no public API. Emitted only when
/// [`rc_stats_codegen_enabled`] is true.
fn emit_rc_stat_call<M: Module>(builder: &mut FunctionBuilder, module: &mut M, symbol: &str) {
    let mut sig = module.make_signature();
    sig.returns.push(AbiParam::new(types::I64));
    if let Ok(id) = module.declare_function(symbol, cranelift_module::Linkage::Import, &sig) {
        let stat_ref = module.declare_func_in_func(id, builder.func);
        builder.ins().call(stat_ref, &[]);
    }
}

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

    // FIXME 0494 localization: when the codegen-time gate is on, emit a call to
    // `runtime/rc_dec_check(ptr)` immediately before the inline atomic sub, so a dec
    // of an already-freed heap pointer aborts AT the stale dec (with the pointer +
    // JIT stack) instead of silently corrupting a reused chunk. Off by default ⇒ no
    // emitted call ⇒ byte-identical codegen.
    if rc_dec_check_enabled() {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        if let Ok(check_id) =
            module.declare_function("runtime/rc_dec_check", cranelift_module::Linkage::Import, &sig)
        {
            let check_ref = module.declare_func_in_func(check_id, builder.func);
            builder.ins().call(check_ref, &[ptr]);
        }
    }

    // S99 stats: count the dec (placed after the nullary skip so bare tags,
    // which never reach here, are not counted).
    if rc_stats_codegen_enabled() {
        emit_rc_stat_call(builder, module, "runtime/rc_stat_dec");
    }
    let rc_addr = builder
        .ins()
        .iadd_imm(ptr, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    let old_rc = if nonatomic_rc_codegen_enabled() {
        // S99 measurement-only NON-ATOMIC dec — UNSOUND above one worker. The
        // pre-decrement value stands in for the atomic_rmw's returned old value.
        let cur = builder.ins().load(types::I64, MemFlags::trusted(), rc_addr, 0);
        let new = builder.ins().isub(cur, one);
        builder.ins().store(MemFlags::trusted(), new, rc_addr, 0);
        cur
    } else {
        builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Sub,
            rc_addr,
            one,
        )
    };

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
        ty: &ConcreteType,
        symbol_tables: Option<&dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>>,
    ) -> HeapCategory
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        // S84 Phase 3 (concrete-boundary-type.md §3.1, FIXME 0391). `classify`
        // takes a `ConcreteType` — a boundary type with NO `Var` and NO
        // `TyConApp` variant. The two non-total arms of the old `Type`-keyed
        // `classify` (`Type::Var => Mixed`, `Type::TyConApp => Mixed`) are
        // **inexpressible** here, so they are DELETED: a representation-
        // undetermined type can no longer be HANDED to `classify` (Principle 18 —
        // the illegal state is unconstructable). The match is exhaustive over the
        // six `ConcreteType` variants with NO catch-all and NO panic case;
        // `classify` is now **total**. The four behavioural `Var`-guards the
        // belt-and-braces 0375/0379 era carried collapse to this one structural
        // property — the §3.11.1 ambiguity is caught upstream at the typecheck
        // check + the `MonoExpr::from_expr` conversion choke point, never here.
        match ty {
            ConcreteType::Int | ConcreteType::Bool | ConcreteType::Float => {
                HeapCategory::NeverHeap
            }
            ConcreteType::String => HeapCategory::AlwaysHeap,
            ConcreteType::Fn(_, _) => {
                // In Ring 0, functions are bare pointers (NeverHeap).
                // In Ring 1+, closures are heap-allocated.
                // Conservative: AlwaysHeap (closures are the common case after Ring 0).
                HeapCategory::AlwaysHeap
            }
            ConcreteType::ADT(fqtn, _) => Self::classify_adt(fqtn, symbol_tables),
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
mod heap_category_tests;


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
expr: &cranelisp_types::MonoExpr,
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

/// Collect variable uses for a call sub-expression, *skipping* a direct
/// top-level `Var` (its occurrence is recorded separately by the `Apply` arm,
/// ordered after all nested uses — see the comment there). For any non-`Var`
/// expression this is identical to `collect_var_uses`.
fn collect_var_uses_nested_only(
expr: &cranelisp_types::MonoExpr,
uses: &mut HashMap<cranelisp_types::Symbol, Vec<cranelisp_types::Span>>,
) {
    if matches!(expr, cranelisp_types::MonoExpr::Var { .. }) {
        // Direct Var: recorded by the caller after nested uses.
        return;
    }
    collect_var_uses(expr, uses);
}

/// Collect all variable references in pre-order traversal.
fn collect_var_uses(
expr: &cranelisp_types::MonoExpr,
uses: &mut HashMap<cranelisp_types::Symbol, Vec<cranelisp_types::Span>>,
) {
    use cranelisp_types::MonoExpr;

    match expr {
        MonoExpr::Var { name, span, .. } => {
            uses.entry(name.clone()).or_default().push(*span);
        }
        MonoExpr::Let { bindings, body, .. } => {
            for (_, val) in bindings {
                collect_var_uses(val, uses);
            }
            collect_var_uses(body, uses);
        }
        MonoExpr::If { cond, then_branch, else_branch, .. } => {
            collect_var_uses(cond, uses);
            collect_var_uses(then_branch, uses);
            collect_var_uses(else_branch, uses);
        }
        MonoExpr::Lambda { body, .. } => {
            collect_var_uses(body, uses);
        }
        MonoExpr::Apply { callee, args, .. } => {
            // Evaluation/consumption order is NOT pre-order textual order. A
            // direct `Var` argument (or callee) is *held* from the moment it is
            // evaluated until the call executes — i.e. until AFTER every sibling
            // argument has been evaluated. So a direct-Var occurrence outlives
            // any use of the same variable nested deeper inside a sibling
            // argument, regardless of textual position.
            //
            // The naive "last textual occurrence is the last use" heuristic gets
            // this wrong for self-recursive tail calls: in
            //   (loop v (sub n 1) (... (vec-push v "z") ...))
            // the direct arg `v` (occurrence #1) is textually BEFORE the nested
            // `(vec-push v …)` (occurrence #2), so #2 was marked last-use. But
            // the tail call re-passes `v` into the next iteration (the backend
            // lowers it to a `jump` reusing the binding — see ring2-rc.md §"TCO+
            // RC"), so `v` is live across iterations. Marking the `vec-push` use
            // as last-use let Vec COW mutate `v` in place and then drop the
            // aliased result as a temporary → use-after-free (DEF-2 / T2). See
            // ring2-rc.md §5.5 for the sibling captured/borrowed-var rules.
            //
            // Fix: record direct-Var occurrences of callee+args AFTER recursing
            // into the nested (non-direct-Var) subexpressions, so a direct-Var
            // arg correctly counts as the latest live use within this call.
            collect_var_uses_nested_only(callee, uses);
            for arg in args {
                collect_var_uses_nested_only(arg, uses);
            }
            if let MonoExpr::Var { name, span, .. } = callee.as_ref() {
                uses.entry(name.clone()).or_default().push(*span);
            }
            for arg in args {
                if let MonoExpr::Var { name, span, .. } = arg {
                    uses.entry(name.clone()).or_default().push(*span);
                }
            }
        }
        MonoExpr::Match { scrutinee, arms, .. } => {
            collect_var_uses(scrutinee, uses);
            for arm in arms {
                collect_var_uses(&arm.body, uses);
            }
        }
        MonoExpr::VecLit { elements, .. } => {
            for e in elements {
                collect_var_uses(e, uses);
            }
        }
        MonoExpr::Trace { body, .. } => {
            collect_var_uses(body, uses);
        }
        MonoExpr::ParBind { bindings, body, .. } => {
            for (_, val_expr) in bindings {
                collect_var_uses(val_expr, uses);
            }
            collect_var_uses(body, uses);
        }
        MonoExpr::LaunchContinue { launched, continuation, .. } => {
            // Union over both sub-trees — the launched effect binds no name (its
            // result is discarded), so var uses come from both arms.
            collect_var_uses(launched, uses);
            collect_var_uses(continuation, uses);
        }
        MonoExpr::ConstrADT { fields, .. } => {
            for f in fields {
                collect_var_uses(f, uses);
            }
        }
        // Literals have no variable references.
        MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::StringLit { .. } => {}
    }
}

#[cfg(test)]
mod tests;
