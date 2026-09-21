//! S121 B5 — `Pure` construction-stamp shape and its closed producer set.

use super::{PURE_GLUE_ABS_OFFSET, append_runtime_ctor_fields, pure_payload_type};
use crate::{drop_glue::DropGlueRegistry, heap::HeapAdt, test_support::make_object_module};
use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};
use cranelisp_types::{ConcreteType, FQTypeName, ModuleFullPath, SymbolTable, TypeName};
use dashmap::DashMap;

fn io_type() -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO"))
}

fn concrete_io(payload: ConcreteType) -> ConcreteType {
    ConcreteType::ADT(io_type(), vec![payload])
}

/// Emit only the central field-selection seam. Both returned values are used so
/// the CLIF text retains the hidden witness definition for inspection.
fn stamp_clif(
    payload: ConcreteType,
    stack: bool,
) -> Result<String, cranelisp_types::CranelispError> {
    let mut module = make_object_module();
    let mut dealloc_sig = module.make_signature();
    dealloc_sig.params.push(AbiParam::new(types::I64));
    let dealloc = module
        .declare_function("runtime/dealloc", Linkage::Import, &dealloc_sig)
        .expect("declare dealloc");
    let mut glue = DropGlueRegistry::new(ModuleFullPath::from("user"), dealloc, None);
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();

    let mut ctx = module.make_context();
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.returns.push(AbiParam::new(types::I64));
    let mut fb_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let payload_value = builder.block_params(entry)[0];

    let fields = append_runtime_ctor_fields(
        &mut builder,
        &mut module,
        &mut glue,
        &tables,
        &io_type(),
        cranelisp_platform::IO_TAG_PURE as usize,
        &concrete_io(payload),
        &[payload_value],
        stack,
        cranelisp_types::Span::SYNTHETIC,
    )?;
    assert_eq!(
        fields.len(),
        2,
        "Pure has one authored and one hidden field"
    );
    let witness_observer = builder.ins().iadd(fields[0], fields[1]);
    builder.ins().return_(&[witness_observer]);
    builder.finalize();
    Ok(format!("{}", ctx.func.display()))
}

// spec: design/backend/non-concrete-release-contract.md §5.1/§5.3 — field 0 remains the
// language payload and the hidden witness is field 1 at absolute offset 32.
#[test]
fn pure_hidden_field_extends_the_payload_without_moving_field_zero() {
    assert_eq!(HeapAdt::field_offset(0), 24);
    assert_eq!(PURE_GLUE_ABS_OFFSET, HeapAdt::field_offset(1) as i64);
    assert_eq!(PURE_GLUE_ABS_OFFSET, 32);
    assert_eq!(HeapAdt::payload_size(2), 24);
}

// spec: design/backend/non-concrete-release-contract.md §5.3 — the self-description question
// has one derivation and answers only for canonical primitives/IO.Pure.
#[test]
fn only_canonical_io_pure_requests_a_hidden_payload_witness() {
    let io_string = concrete_io(ConcreteType::String);
    assert_eq!(
        pure_payload_type(
            &io_type(),
            cranelisp_platform::IO_TAG_PURE as usize,
            &io_string,
            1,
        )
        .unwrap(),
        Some(&ConcreteType::String),
    );
    assert!(
        pure_payload_type(
            &io_type(),
            cranelisp_platform::IO_TAG_EFFECT as usize,
            &io_string,
            1,
        )
        .unwrap()
        .is_none(),
    );
    let user_io = FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("IO"));
    assert!(
        pure_payload_type(
            &user_io,
            cranelisp_platform::IO_TAG_PURE as usize,
            &ConcreteType::ADT(user_io.clone(), vec![ConcreteType::String]),
            1,
        )
        .unwrap()
        .is_none(),
    );
}

// spec: design/backend/non-concrete-release-contract.md §5.3 — owning payloads carry the
// canonical registry function address; scalars and stack-placed Pure carry 0.
#[test]
fn pure_witness_is_canonical_glue_for_heap_and_zero_for_scalar() {
    let heap = stamp_clif(ConcreteType::String, false).expect("heap Pure stamp");
    assert!(
        heap.contains("func_addr.i64"),
        "heap payload needs glue:\n{heap}"
    );
    assert!(
        !heap.contains("iconst.i64 1"),
        "construction never emits Claimed(1):\n{heap}"
    );

    let scalar = stamp_clif(ConcreteType::Int, false).expect("scalar Pure stamp");
    assert!(
        scalar.contains("iconst.i64 0"),
        "scalar payload stamps 0:\n{scalar}"
    );
    assert!(
        !scalar.contains("func_addr"),
        "scalar payload owns no glue:\n{scalar}"
    );

    let stack_scalar = stamp_clif(ConcreteType::Int, true).expect("stack scalar Pure stamp");
    assert!(stack_scalar.contains("iconst.i64 0"));
    let err = stamp_clif(ConcreteType::String, true).expect_err("owning stack Pure must refuse");
    assert!(err.to_string().contains("stack-placed Pure"), "{err}");
}

// spec: design/backend/non-concrete-release-contract.md §5.3 — exactly three compiled-code
// construction paths call the one derivation seam. The fourth producer is the
// distinct post-platform-call adoption store in `stamp_platform_return`.
#[test]
fn pure_construction_stamp_has_exactly_three_call_sites() {
    let apply = include_str!("../apply.rs");
    let as_value = include_str!("../control_flow/fn_as_value.rs");
    // apply.rs contains the direct Apply and ConstrADT calls;
    // fn_as_value.rs contains the constructor-wrapper call.
    assert_eq!(apply.matches("append_runtime_ctor_fields(").count(), 2);
    assert_eq!(as_value.matches("append_runtime_ctor_fields(").count(), 1);
}
