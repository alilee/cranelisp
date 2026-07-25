use super::{is_trace_typed_concrete, trace_accessor_abi_name};
use cranelisp_types::{ConcreteType, FQTypeName, ModuleFullPath, TypeName};

#[test]
fn accessor_names_map_to_intrinsics() {
    assert_eq!(
        trace_accessor_abi_name("nanos"),
        Some("cranelisp_trace_nanos")
    );
    assert_eq!(
        trace_accessor_abi_name("name"),
        Some("cranelisp_trace_name")
    );
    assert_eq!(
        trace_accessor_abi_name("params"),
        Some("cranelisp_trace_params")
    );
    assert_eq!(
        trace_accessor_abi_name("result"),
        Some("cranelisp_trace_result")
    );
    assert_eq!(
        trace_accessor_abi_name("children"),
        Some("cranelisp_trace_children")
    );
}

#[test]
fn non_accessor_names_do_not_map() {
    // first_child_nanos is the /run-tests internal reader, not a field
    // accessor — it must NOT be rewritten via this path.
    assert_eq!(trace_accessor_abi_name("first_child_nanos"), None);
    assert_eq!(trace_accessor_abi_name("nano"), None);
    assert_eq!(trace_accessor_abi_name("foo"), None);
    assert_eq!(trace_accessor_abi_name(""), None);
}

fn trace_adt() -> ConcreteType {
    ConcreteType::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Trace")),
        vec![],
    )
}

#[test]
fn trace_receiver_is_scoped() {
    assert!(is_trace_typed_concrete(&trace_adt()));
}

#[test]
fn non_trace_receiver_is_rejected() {
    // A user ADT named Trace in a different module must not be hijacked.
    let user_trace = ConcreteType::ADT(
        FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Trace")),
        vec![],
    );
    assert!(!is_trace_typed_concrete(&user_trace));
    // A same-name field on an unrelated primitives ADT.
    let other = ConcreteType::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Option")),
        vec![ConcreteType::Int],
    );
    assert!(!is_trace_typed_concrete(&other));
    assert!(!is_trace_typed_concrete(&ConcreteType::Int));
}
