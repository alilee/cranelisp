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

use cranelisp_types::{FQTypeName, HeapHeader, ModuleEntry, ModuleFullPath, Symbol, SymbolTable};

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
pub fn is_mixed_adt(symbol_tables: &DashMap<ModuleFullPath, SymbolTable>, fqtn: &FQTypeName) -> bool {
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
        Expr::Var { name, span } => {
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
            callee: Box::new(Expr::Var { name: Symbol::from("f"), span: Span::new(0, 1) }),
            args: vec![
                Expr::Var { name: x.clone(), span: Span::new(2, 3) },
                Expr::Var { name: x.clone(), span: Span::new(4, 5) },
            ],
            span: Span::new(0, 6),
        };

        let last_uses = compute_last_uses(&expr);
        // First use of x is NOT last use.
        assert_eq!(last_uses.get(&(x.clone(), Span::new(2, 3))), Some(&false));
        // Second use of x IS last use.
        assert_eq!(last_uses.get(&(x.clone(), Span::new(4, 5))), Some(&true));
    }
}
