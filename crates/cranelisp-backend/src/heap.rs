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
use cranelift_jit::JITModule;

use cranelisp_types::{HeapHeader, TypeDefInfo, TypeName};

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

/// Closure: [header | code_ptr | cap_0 | cap_1 | ... | cap_n]
#[repr(C)]
pub struct HeapClosure {
    pub header: HeapHeader,
    /// Pointer to the compiled lambda body.
    /// Lambda body signature: (env_ptr: i64, params...) -> i64
    pub code_ptr: i64,
    // Captures follow at CAPTURES_START. Each capture is an i64.
}

impl HeapClosure {
    pub const CODE_PTR_OFFSET: i32 = offset_of!(Self, code_ptr) as i32; // 16
    pub const CAPTURES_START: usize = mem::size_of::<Self>(); // 24

    /// Offset of the i-th captured value from the base pointer.
    pub const fn capture_offset(i: usize) -> i32 {
        (Self::CAPTURES_START + i * mem::size_of::<i64>()) as i32
    }

    /// Payload size after the header: code_ptr + n captures.
    pub const fn payload_size(capture_count: usize) -> usize {
        mem::size_of::<i64>() + capture_count * mem::size_of::<i64>()
    }
}

const _: () = assert!(HeapClosure::CODE_PTR_OFFSET == 16);
const _: () = assert!(HeapClosure::CAPTURES_START == 24);

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

/// Emit inline atomic RC decrement + conditional dealloc.
///
/// old = atomic_rmw(Sub, ptr + RC_OFFSET, 1, Release)
/// if old == 1:
///     fence(Acquire)
///     call drop_glue(ptr)   [if type has heap fields]
///     call runtime/dealloc(ptr)
///
/// The `dealloc_func_id` is the FuncId for `runtime/dealloc`.
/// The `drop_glue_id` is Some(FuncId) if the type has heap-typed fields.
pub fn emit_rc_dec(
    builder: &mut FunctionBuilder,
    module: &mut JITModule,
    ptr: Value,
    dealloc_func_id: FuncId,
    drop_glue_id: Option<FuncId>,
) {
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
    let cont_block = builder.create_block();

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
pub fn emit_alloc(
    builder: &mut FunctionBuilder,
    module: &mut JITModule,
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
pub fn is_mixed_adt(type_defs: &HashMap<TypeName, TypeDefInfo>, type_name: &TypeName) -> bool {
    if let Some(info) = type_defs.get(type_name) {
        let has_nullary = info.constructors.iter().any(|c| c.fields.is_empty());
        let has_data = info.constructors.iter().any(|c| !c.fields.is_empty());
        has_nullary && has_data
    } else {
        false
    }
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
        Expr::RunTests { init, pass_fn, fail_fn, .. } => {
            collect_var_uses(init, uses);
            collect_var_uses(pass_fn, uses);
            collect_var_uses(fail_fn, uses);
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

    #[test]
    fn test_heap_adt_layout() {
        assert_eq!(HeapAdt::TAG_OFFSET, 16);
        assert_eq!(HeapAdt::FIELDS_START, 24);
        assert_eq!(HeapAdt::field_offset(0), 24);
        assert_eq!(HeapAdt::field_offset(1), 32);
        assert_eq!(HeapAdt::payload_size(0), 8); // tag only
        assert_eq!(HeapAdt::payload_size(2), 24); // tag + 2 fields
    }

    #[test]
    fn test_heap_closure_layout() {
        assert_eq!(HeapClosure::CODE_PTR_OFFSET, 16);
        assert_eq!(HeapClosure::CAPTURES_START, 24);
        assert_eq!(HeapClosure::capture_offset(0), 24);
        assert_eq!(HeapClosure::capture_offset(1), 32);
        assert_eq!(HeapClosure::payload_size(0), 8); // code_ptr only
        assert_eq!(HeapClosure::payload_size(3), 32); // code_ptr + 3 captures
    }

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
