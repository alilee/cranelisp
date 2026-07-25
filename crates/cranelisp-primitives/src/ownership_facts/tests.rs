use cranelisp_types::{Mode, ResultMode, Type};

use super::{alias_of_zero, copy_fresh_for_type, uniform_for_type, vec_get, vec_push, vec_set};

#[test]
fn constructors_pin_each_ownership_vocabulary_shape() {
    let copy = copy_fresh_for_type(&Type::Fn(vec![Type::Int, Type::Bool], Box::new(Type::Int)));
    assert_eq!(copy.param_modes, vec![Mode::Copy, Mode::Copy]);
    assert_eq!(copy.result, ResultMode::Fresh);

    let borrowed = uniform_for_type(
        &Type::Fn(vec![Type::String], Box::new(Type::Int)),
        Mode::Borrowed,
    );
    assert_eq!(borrowed.param_modes, vec![Mode::Borrowed]);

    assert_eq!(alias_of_zero().result, ResultMode::AliasOf(0));
    assert_eq!(vec_get().result, ResultMode::ProjectionOf(0));
    assert_eq!(vec_set().result, ResultMode::MayAliasOf(0));
    assert_eq!(vec_push().result, ResultMode::MayAliasOf(0));
}

#[test]
#[should_panic(expected = "copy/fresh declaration contains a heap parameter")]
fn copy_constructor_rejects_heap_parameters() {
    let _ = copy_fresh_for_type(&Type::Fn(vec![Type::String], Box::new(Type::String)));
}
