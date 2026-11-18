//! Heap layout types, RC emit helpers, and codegen heap classification.
//!
//! Owns the backend's heap layout structs (`HeapAdt`, `HeapClosure`,
//! `HeapVec`) over the types-owned `HeapHeader`, and the inline RC and
//! allocation emitters other codegen calls rather than spelling offsets. The
//! layouts are `pub` for the binary crate's value display and test runner.
//! `cranelisp-intrinsics` cannot depend on this crate and carries its own
//! offsets for the same layouts.
//!
//! [`HeapCategory`] + [`HeapCategory::classify`] are the codegen heap
//! classification. `classify` carries a two-mode `Option<&tables>` contract
//! (pre-typecheck: ADTs conservatively `Mixed`; post-typecheck: classified by
//! constructor inspection), noted at the item.

use std::mem::{self, offset_of};

use cranelift::prelude::*;
use cranelift_codegen::ir::AtomicRmwOp;
use cranelift_module::{FuncId, Module};

use dashmap::DashMap;

use cranelisp_types::{
    CallableOrigin, ConcreteType, FQTypeName, HeapHeader, ModuleFullPath, Symbol, SymbolTable,
};

use cranelisp_types::NULLARY_TAG_THRESHOLD;

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
    pub const LEN_OFFSET: i32 = offset_of!(Self, len) as i32; // 16
    pub const CAP_OFFSET: i32 = offset_of!(Self, cap) as i32; // 24
    pub const DATA_PTR_OFFSET: i32 = offset_of!(Self, data_ptr) as i32; // 32

    /// Payload size after the header: len + cap + data_ptr.
    pub const fn payload_size() -> usize {
        3 * mem::size_of::<i64>() // 24 bytes
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

/// Whether an inline RC operation takes the plain (non-atomic) arm: only when
/// the `CRANELISP_NONATOMIC_RC` probe is set (`design/backend/ownership-codegen.md`
/// §5.1). Tallies the decision, at codegen time, for `[RC_STATS]`'s
/// `rc_nonatomic`/`rc_atomic` split. Call once per emitted operation.
pub(crate) fn use_nonatomic_arm() -> bool {
    let nonatomic = nonatomic_rc_codegen_enabled();
    cranelisp_intrinsics::rc::tally_rc_emit(nonatomic);
    nonatomic
}

/// The emission tally [`use_nonatomic_arm`] writes, `(non_atomic_ops,
/// total_ops)`. Its state is `cranelisp-intrinsics::rc`'s, which also prints it
/// at exit, so these tests and the `[RC_STATS]` line read one count.
#[allow(dead_code)]
pub(crate) fn rc_emit_counts() -> (u64, u64) {
    cranelisp_intrinsics::rc::rc_emit_counts()
}

/// Emit an inline RC increment: `atomic_rmw(Add, ptr + RC_OFFSET, 1)`, or a
/// plain load/`iadd`/store under the probe ([`use_nonatomic_arm`]).
///
/// `module` is used only by the `CRANELISP_RC_STATS` gate, which emits a
/// `runtime/rc_stat_inc` call first.
pub(crate) fn emit_rc_inc<M: Module>(builder: &mut FunctionBuilder, module: &mut M, ptr: Value) {
    emit_rc_stat_call_gated(builder, module, "runtime/rc_stat_inc");
    let rc_addr = builder
        .ins()
        .iadd_imm(ptr, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    emit_rc_add(builder, rc_addr, one);
}

/// The count update shared by both increments.
fn emit_rc_add(builder: &mut FunctionBuilder, rc_addr: Value, one: Value) {
    if use_nonatomic_arm() {
        let cur = builder
            .ins()
            .load(types::I64, MemFlags::trusted(), rc_addr, 0);
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

/// The nullary-tag skip guard shared by BOTH guarded RC halves. Emits the
/// predicate, branches on it, and switches the builder into the guarded block.
///
/// ONE predicate, one home (the crate's ONE-predicate pattern, `AGENTS.md`
/// §"RC-emission gates that are ONE predicate"; Principle 18). The emitted shape
/// is
///
/// ```text
///   is_tag = icmp ult ptr, NULLARY_TAG_THRESHOLD
///   brif is_tag, cont_block, guarded_block
/// ```
///
/// so the RC op in `guarded_block` executes **iff `ptr >= NULLARY_TAG_THRESHOLD`**
/// — a real heap pointer, which is the only thing carrying an RC header — while a
/// bare nullary ADT tag branches straight to `cont_block`.
///
/// Deriving that decision here rather than at each half is what makes a polarity
/// GAP between the inc and the dec unrepresentable: an edit to this body moves
/// both halves together, and a divergence between "what the inc treats as a
/// pointer" and "what the dec does" has no way to be spelled (invariant I-CT,
/// `design/backend/transitive-drop-glue.md` §4.1). The remaining risk this cannot
/// close is the ABSOLUTE polarity — inverting the comparison here inverts both
/// halves consistently — which is pinned structurally, as control flow, by
/// `compiler/fn_compiler/ctor_template_admission_tests.rs::assert_threshold_guarded_rmws`
/// (FIXME 0905).
///
/// The caller creates `cont_block` FIRST: block creation order is CLIF block
/// numbering, and both call sites' emission is byte-identical to the hand-rolled
/// prologues this replaced.
fn emit_nullary_skip_guard(builder: &mut FunctionBuilder, ptr: Value, cont_block: Block) {
    let guarded_block = builder.create_block();
    let threshold = builder.ins().iconst(types::I64, NULLARY_THRESHOLD_I64);
    let is_tag = builder.ins().icmp(IntCC::UnsignedLessThan, ptr, threshold);
    builder
        .ins()
        .brif(is_tag, cont_block, &[], guarded_block, &[]);
    builder.switch_to_block(guarded_block);
    builder.seal_block(guarded_block);
}

/// Emit an inline RC increment that skips a bare nullary tag (a value below
/// `NULLARY_TAG_THRESHOLD`, which has no RC header). Otherwise as [`emit_rc_inc`].
pub(crate) fn emit_rc_inc_guarded<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    ptr: Value,
) {
    let cont_block = builder.create_block();
    emit_nullary_skip_guard(builder, ptr, cont_block);

    // S99 stats: count only a real inc (bare nullary tags took the skip branch).
    emit_rc_stat_call_gated(builder, module, "runtime/rc_stat_inc");
    let rc_addr = builder
        .ins()
        .iadd_imm(ptr, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    emit_rc_add(builder, rc_addr, one);

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

/// Emit `runtime/rc_dec_check(ptr)` immediately before an inline dec, gated on
/// the codegen-time `CRANELISP_RC_DEC_CHECK` switch (§15 row 6, the tier-3
/// category-B seam). A dec of an already-freed heap pointer then aborts AT the
/// stale dec (with the pointer + JIT stack) instead of silently corrupting a
/// reused chunk. Off by default ⇒ no emitted call ⇒ **byte-identical codegen**.
///
/// The ONE seam (Principle 7) every backend-emitted inline dec routes its check
/// through: the header-dec path ([`emit_rc_dec_guarded`]) AND the
/// Vec-aware dec (`vec_codegen::emit_vec_rc_dec_with_drop` — the COW
/// copy-branch source release + every vec teardown/scope-exit dec), so the
/// DEC_CHECK lane sees EVERY backend dec, not only the header-dec inline.
pub(crate) fn emit_rc_dec_check_gated<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    ptr: Value,
) {
    if rc_dec_check_enabled() {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        if let Ok(check_id) = module.declare_function(
            "runtime/rc_dec_check",
            cranelift_module::Linkage::Import,
            &sig,
        ) {
            let check_ref = module.declare_func_in_func(check_id, builder.func);
            builder.ins().call(check_ref, &[ptr]);
        }
    }
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
pub(crate) fn rc_stats_codegen_enabled() -> bool {
    static E: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *E.get_or_init(|| std::env::var_os("CRANELISP_RC_STATS").is_some())
}

/// Emit a zero-arg `runtime/*` tally-helper call under the codegen-time
/// `CRANELISP_RC_STATS` gate (a no-op when the gate is off, so callers may invoke
/// unconditionally). The increment-II reuse/COW arms (`vec_codegen`) and the
/// `str-len` per-extern adaptation site (`apply`) reach the stats surface through
/// this one seam (Principle 7). Off ⇒ no emitted IR ⇒ byte-identical codegen.
pub(crate) fn emit_rc_stat_call_gated<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    symbol: &str,
) {
    if rc_stats_codegen_enabled() {
        emit_rc_stat_call(builder, module, symbol);
    }
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
///
/// The count update is `atomic_rmw(Sub)`, or a plain load/`isub`/store under
/// the probe ([`use_nonatomic_arm`]); the `old == 1` free path is the same in
/// both.
pub(crate) fn emit_rc_dec_guarded<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    ptr: Value,
    dealloc_func_id: FuncId,
    drop_glue_id: Option<FuncId>,
    guard_nullary: bool,
) {
    let cont_block = builder.create_block();

    // Guard: if value is a bare nullary tag, skip the dec entirely. Same
    // predicate, same polarity as the inc half — see `emit_nullary_skip_guard`.
    if guard_nullary {
        emit_nullary_skip_guard(builder, ptr, cont_block);
    }

    // FIXME 0494 localization (§15 row 6 — via the shared `emit_rc_dec_check_gated`
    // seam): when the codegen-time gate is on, emit `runtime/rc_dec_check(ptr)`
    // immediately before the inline atomic sub, so a dec of an already-freed heap
    // pointer aborts AT the stale dec instead of silently corrupting a reused
    // chunk. Off by default ⇒ no emitted call ⇒ byte-identical codegen.
    emit_rc_dec_check_gated(builder, module, ptr);

    // S99 stats: count the dec (placed after the nullary skip so bare tags,
    // which never reach here, are not counted).
    emit_rc_stat_call_gated(builder, module, "runtime/rc_stat_dec");
    let rc_addr = builder
        .ins()
        .iadd_imm(ptr, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    let old_rc = if use_nonatomic_arm() {
        // The pre-decrement value stands in for the atomic_rmw's returned old value.
        let cur = builder
            .ins()
            .load(types::I64, MemFlags::trusted(), rc_addr, 0);
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

    builder.ins().brif(cmp, free_block, &[], cont_block, &[]);

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
    symbol_tables
        .get(&fqtn.module)
        .map(|table| {
            // Constructor name-list via the SINGLE shared
            // `cranelisp_types::type_ctor_names` reader (FIXME 0528 mirror cure) —
            // a product is never mixed (one ctor), but resolve uniformly. `None`
            // (non-type entry) ⇒ not mixed.
            let Some(ctor_names) = cranelisp_types::type_ctor_names(table.value(), fqtn) else {
                return false;
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
fn ctor_field_count<C, L>(table: &SymbolTable<C, L>, ctor_name: &Symbol) -> Option<usize>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // S79 Option 3a: product ctors are got-slotted `Def`s exactly like sum
    // ctors (with a `type_def: Some(..)` facet), so the one `Def` arm covers
    // both — its `field_count` is the arity. The prior `TypeDef`-with-
    // `constructor_scheme` product leg is retired.
    table
        .get(ctor_name.as_ref())
        .and_then(cranelisp_types::Binding::callable)
        .and_then(|callable| match &callable.origin {
            CallableOrigin::Ctor { field_count, .. } => Some(*field_count),
            _ => None,
        })
}

/// Threshold constant for discriminating nullary tags from heap pointers.
pub(crate) const NULLARY_THRESHOLD_I64: i64 = NULLARY_TAG_THRESHOLD as i64;

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
            ConcreteType::Int | ConcreteType::Bool | ConcreteType::Float => HeapCategory::NeverHeap,
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

        // The constructor name-list (from a `TypeDef` sum/enum entry OR a
        // single-ctor product ctor `Def`'s `type_def` facet, S79 Option 3a) is
        // resolved by the SINGLE shared `cranelisp_types::type_ctor_names` reader
        // — no backend-local copy of the `TypeDef`-vs-product-facet switch
        // (FIXME 0528 mirror cure; the same resolver `value_layout` delegates to).
        let Some(ctor_names) = cranelisp_types::type_ctor_names(table.value(), fqtn) else {
            return HeapCategory::Mixed;
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

#[cfg(test)]
mod tests;
