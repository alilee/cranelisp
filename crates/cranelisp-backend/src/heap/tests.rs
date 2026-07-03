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
    use cranelisp_types::{ConcreteType, MonoExpr, Span, Symbol};

    let x = Symbol::from("x");
    let var = |name: Symbol, span: Span| MonoExpr::Var {
        name,
        span,
        resolved_call: None,
        ty: ConcreteType::Int,
    };
    let expr = MonoExpr::Apply {
        callee: Box::new(var(Symbol::from("f"), Span::new(0, 1))),
        args: vec![
            var(x.clone(), Span::new(2, 3)),
            var(x.clone(), Span::new(4, 5)),
        ],
        span: Span::new(0, 6),
        resolved_call: None,
        ty: ConcreteType::Int,
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
    };

    let last_uses = compute_last_uses(&expr);
    // First use of x is NOT last use.
    assert_eq!(last_uses.get(&(x.clone(), Span::new(2, 3))), Some(&false));
    // Second use of x IS last use.
    assert_eq!(last_uses.get(&(x.clone(), Span::new(4, 5))), Some(&true));
}

// spec: 12-runtime §12.3.3 — last-use must follow consumption order, not
// textual pre-order: a direct `Var` argument to a call is held until the
// call executes, so it outlives any use of the same var nested inside a
// SIBLING argument — even when that nested use is textually later. This is
// the seam of the DEF-2/T2 vec-push borrowed-recursive use-after-free:
// `(loop v (sub n 1) (... (vec-push v "z") ...))` — the direct `v` arg
// (span 2..3, occurrence #1) must be last-use; the nested `vec-push v`
// (span 10..11, occurrence #2) must NOT, so Vec COW takes the copy path
// instead of mutating the still-live `v` in place. Regression: a naive
// textual-last heuristic marks the nested use last and corrupts `v`.
#[test]
fn last_use_direct_arg_outlives_nested_sibling_arg() {
    use cranelisp_types::{ConcreteType, MonoExpr, Span, Symbol};

    let v = Symbol::from("v");
    let var = |name: Symbol, span: Span, ty: ConcreteType| MonoExpr::Var {
        name,
        span,
        resolved_call: None,
        ty,
    };
    let vec_ty = ConcreteType::Int; // type is irrelevant to last-use ordering

    // (loop v (g) (h (vec-push v ...)))  modelled as nested Applys:
    //   callee = loop
    //   arg0   = v                      (direct Var, occurrence #1, span 2..3)
    //   arg1   = (g)                    (no v)
    //   arg2   = (h (push v))           v nested deep, occurrence #2, span 10..11
    let inner_push = MonoExpr::Apply {
        callee: Box::new(var(Symbol::from("vec-push"), Span::new(8, 9), vec_ty.clone())),
        args: vec![var(v.clone(), Span::new(10, 11), vec_ty.clone())],
        span: Span::new(7, 12),
        resolved_call: None,
        ty: vec_ty.clone(),
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
    };
    let arg2 = MonoExpr::Apply {
        callee: Box::new(var(Symbol::from("h"), Span::new(6, 7), vec_ty.clone())),
        args: vec![inner_push],
        span: Span::new(5, 13),
        resolved_call: None,
        ty: vec_ty.clone(),
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
    };
    let arg1 = MonoExpr::Apply {
        callee: Box::new(var(Symbol::from("g"), Span::new(4, 5), vec_ty.clone())),
        args: vec![],
        span: Span::new(4, 6),
        resolved_call: None,
        ty: vec_ty.clone(),
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
    };
    let expr = MonoExpr::Apply {
        callee: Box::new(var(Symbol::from("loop"), Span::new(0, 1), vec_ty.clone())),
        args: vec![var(v.clone(), Span::new(2, 3), vec_ty.clone()), arg1, arg2],
        span: Span::new(0, 14),
        resolved_call: None,
        ty: vec_ty,
        confined: None,
        escapes: None,
        provenance: None,
        unique_static: None,
    };

    let last_uses = compute_last_uses(&expr);
    // The direct recursive-call argument `v` is the LAST live use.
    assert_eq!(
        last_uses.get(&(v.clone(), Span::new(2, 3))),
        Some(&true),
        "direct call-arg occurrence of v must be last-use"
    );
    // The textually-later nested `(vec-push v ...)` use is NOT last-use.
    assert_eq!(
        last_uses.get(&(v.clone(), Span::new(10, 11))),
        Some(&false),
        "nested-in-sibling-arg occurrence of v must NOT be last-use"
    );
}

// spec: sprints/SPRINT.md §"Wave 0" R4 — byte-identical-off guard for the RC
// inc codegen switch. With both S99 env gates unset (the test-process default),
// `emit_rc_inc` must emit the blessed inline `atomic_rmw` and NO `rc_stat_inc`
// tally call — i.e. the pre-S99 emission, unchanged.
#[test]
fn s99_emit_rc_inc_default_is_atomic_rmw_no_stat() {
    use crate::jit::Jit;
    use cranelift::prelude::*;

    let mut jit = Jit::new_with_symbols(&[]).expect("jit construction");
    let module = jit.jit_module();
    let mut ctx = module.make_context();
    ctx.func.signature.params.push(AbiParam::new(types::I64));

    let mut fbc = FunctionBuilderContext::new();
    {
        let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let entry = fb.create_block();
        fb.append_block_params_for_function_params(entry);
        fb.switch_to_block(entry);
        fb.seal_block(entry);
        let ptr = fb.block_params(entry)[0];
        super::emit_rc_inc(&mut fb, module, ptr);
        fb.ins().return_(&[]);
        fb.finalize();
    }
    let clif = ctx.func.display().to_string();

    assert!(
        clif.contains("atomic_rmw"),
        "default RC inc must emit atomic_rmw (byte-identical-off), got:\n{clif}"
    );
    assert!(
        !clif.contains("rc_stat_inc"),
        "RC-stats gate must be off by default (no tally call emitted):\n{clif}"
    );
}
