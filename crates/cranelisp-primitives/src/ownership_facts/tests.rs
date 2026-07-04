//! Scenario matrix for the declared primitive ownership fact-table (Principle
//! 23 — the classifier's strategy seams, organized class × shape). Pins the
//! §13.4 transcription of the `ring2-rc.md` §3.3 audit at construction.

use super::*;
use cranelisp_types::{Mode, ModuleFullPath, ParamFlow, ResultMode, Type, TypeName};

fn fn_ty(params: Vec<Type>, ret: Type) -> Type {
    Type::Fn(params, Box::new(ret))
}

fn option_int() -> Type {
    Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Option"), vec![Type::Int])
}

fn vec_a() -> Type {
    // The element var id is arbitrary — the classifier only cares that it is
    // non-scalar (heap-disposition).
    Type::adt(ModuleFullPath::from("primitives"), TypeName::from("Vec"), vec![Type::Var(0)])
}

// spec: design/typecheck/ownership-inference.md §13.4 — scalar ops are the
// mechanical all-`Copy`/`Fresh` class (zero audit dependency).
#[test]
fn scalar_binary_op_is_all_copy_fresh() {
    let s = declared_mode_summary("add-i64", &fn_ty(vec![Type::Int, Type::Int], Type::Int)).unwrap();
    assert_eq!(s, summary(vec![Mode::Copy, Mode::Copy], Vec::new(), ResultMode::Fresh));
    // Scalar params carry no flow facts (empty ⇒ ⊤ via the accessor, never read
    // for a Copy param).
    assert!(s.param_flow.is_empty());
}

#[test]
fn scalar_unary_op_is_copy_fresh() {
    let s = declared_mode_summary("not", &fn_ty(vec![Type::Bool], Type::Bool)).unwrap();
    assert_eq!(s, summary(vec![Mode::Copy], Vec::new(), ResultMode::Fresh));
}

#[test]
fn to_string_conversion_is_copy_fresh() {
    // Int→String: the arg is scalar (Copy); the fresh String result is `Fresh`.
    let s = declared_mode_summary("int-to-string", &fn_ty(vec![Type::Int], Type::String)).unwrap();
    assert_eq!(s, summary(vec![Mode::Copy], Vec::new(), ResultMode::Fresh));
}

#[test]
fn nullary_all_scalar_is_empty_copy_fresh() {
    let s = declared_mode_summary("some-const", &fn_ty(vec![], Type::Int)).unwrap();
    assert_eq!(s, summary(Vec::new(), Vec::new(), ResultMode::Fresh));
}

// spec: design/typecheck/ownership-inference.md §9.1 — only-read heap params
// are declared `Borrowed` (analysis fact) while the extern keeps `Consumed`.
#[test]
fn only_read_unary_is_borrowed_consumed_fresh() {
    let s = declared_mode_summary("str-len", &fn_ty(vec![Type::String], Type::Int)).unwrap();
    assert_eq!(s, summary(vec![Mode::Borrowed], vec![ParamFlow::Consumed], ResultMode::Fresh));
}

#[test]
fn only_read_binary_predicate_is_borrowed() {
    for name in ["str-eq", "contains?", "starts-with?", "ends-with?"] {
        let s = declared_mode_summary(name, &fn_ty(vec![Type::String, Type::String], Type::Bool))
            .unwrap_or_else(|| panic!("{name} must classify"));
        assert_eq!(
            s,
            summary(
                vec![Mode::Borrowed, Mode::Borrowed],
                vec![ParamFlow::Consumed, ParamFlow::Consumed],
                ResultMode::Fresh,
            ),
            "{name}",
        );
    }
}

// spec: design/backend/ring2-rc.md §3.3 (FIXME 0504) — `neq-string` transcribes
// the audit row (only-read `Borrowed`), even though no `ModuleEntry` currently
// consumes it (shim-only; `Eq.!=` trait dispatch).
#[test]
fn neq_string_transcribes_the_0504_borrowed_row() {
    let s = declared_mode_summary("neq-string", &fn_ty(vec![Type::String, Type::String], Type::Bool))
        .unwrap();
    assert_eq!(s.param_modes, vec![Mode::Borrowed, Mode::Borrowed]);
    assert_eq!(s.result, ResultMode::Fresh);
}

// spec: design/typecheck/ownership-inference.md §13.4 — transforming heap
// leaves are `Owned`/`Consumed`/`Fresh`.
#[test]
fn transforming_heap_is_owned_consumed_fresh() {
    let s = declared_mode_summary("str-concat", &fn_ty(vec![Type::String, Type::String], Type::String))
        .unwrap();
    assert_eq!(
        s,
        summary(
            vec![Mode::Owned, Mode::Owned],
            vec![ParamFlow::Consumed, ParamFlow::Consumed],
            ResultMode::Fresh,
        )
    );
}

#[test]
fn transforming_mixed_heap_and_scalar_params() {
    // substring : [String, Int, Int] → String. Heap arg Owned; scalar args Copy;
    // flow is a full positional vector (scalar positions neutral `Consumed`).
    let s = declared_mode_summary(
        "substring",
        &fn_ty(vec![Type::String, Type::Int, Type::Int], Type::String),
    )
    .unwrap();
    assert_eq!(
        s,
        summary(
            vec![Mode::Owned, Mode::Copy, Mode::Copy],
            vec![ParamFlow::Consumed, ParamFlow::Consumed, ParamFlow::Consumed],
            ResultMode::Fresh,
        )
    );
}

#[test]
fn transforming_producing_heap_adt_result() {
    // parse-int : [String] → (Option Int). Owned/Consumed → Fresh.
    let s = declared_mode_summary("parse-int", &fn_ty(vec![Type::String], option_int())).unwrap();
    assert_eq!(s, summary(vec![Mode::Owned], vec![ParamFlow::Consumed], ResultMode::Fresh));
}

// spec: design/typecheck/ownership-inference.md §9.3 / §13.4 — `string-identity`
// is the one alias leaf; the arg flows out unchanged.
#[test]
fn string_identity_is_the_alias_leaf() {
    let s = declared_mode_summary("string-identity", &fn_ty(vec![Type::String], Type::String))
        .unwrap();
    assert_eq!(s, summary(vec![Mode::Owned], vec![ParamFlow::IntoResult], ResultMode::AliasOf(0)));
}

// spec: design/typecheck/ownership-inference.md §9.3 — the inline vec family's
// projection/COW vocabulary.
#[test]
fn vec_get_is_projection_of_root() {
    let s = declared_mode_summary("vec-get", &fn_ty(vec![vec_a(), Type::Int], Type::Var(0))).unwrap();
    assert_eq!(
        s,
        summary(
            vec![Mode::Borrowed, Mode::Copy],
            vec![ParamFlow::Consumed, ParamFlow::Consumed],
            ResultMode::ProjectionOf(0),
        )
    );
}

#[test]
fn vec_set_copies_and_stores_value_into_result() {
    let s = declared_mode_summary(
        "vec-set",
        &fn_ty(vec![vec_a(), Type::Int, Type::Var(0)], vec_a()),
    )
    .unwrap();
    assert_eq!(
        s,
        summary(
            vec![Mode::Owned, Mode::Copy, Mode::Owned],
            vec![ParamFlow::Consumed, ParamFlow::Consumed, ParamFlow::IntoResult],
            ResultMode::Fresh,
        )
    );
}

#[test]
fn vec_push_stores_value_into_result() {
    let s = declared_mode_summary("vec-push", &fn_ty(vec![vec_a(), Type::Var(0)], vec_a())).unwrap();
    assert_eq!(
        s,
        summary(
            vec![Mode::Owned, Mode::Owned],
            vec![ParamFlow::Consumed, ParamFlow::IntoResult],
            ResultMode::Fresh,
        )
    );
}

#[test]
fn vec_len_is_borrowed_read() {
    let s = declared_mode_summary("vec-len", &fn_ty(vec![vec_a()], Type::Int)).unwrap();
    assert_eq!(s, summary(vec![Mode::Borrowed], vec![ParamFlow::Consumed], ResultMode::Fresh));
}

// spec: design/typecheck/ownership-inference.md §13.4 — the Decision-24
// conservative default: an unclassified heap leaf carries NO declared summary
// (absence ⇒ all-`Owned`/`Fresh` via the ⊤-on-absence accessors).
#[test]
fn unclassified_heap_leaf_is_conservative_default_none() {
    // A hypothetical primitive with a heap param but no audit-row classification.
    let s = declared_mode_summary("mystery-op", &fn_ty(vec![Type::String], Type::String));
    assert!(s.is_none(), "no-audit-row heap leaf must default to None (Decision-24)");
}

#[test]
fn non_fn_type_is_none() {
    assert!(declared_mode_summary("weird", &Type::Int).is_none());
}

// The ABI half of every declared summary is compared through `abi_eq`; a leaf
// whose params are all `Owned`/`Fresh` is ABI-equivalent to `None`. Confirm the
// conservative-default `None` and an all-`Owned` summary agree via the accessor
// home (the ⊤-on-absence contract this fact table relies on).
#[test]
fn borrowed_leaf_is_not_abi_conservative() {
    // A `Borrowed` declared leaf is a genuine ABI refinement (not the ⊤ point),
    // so it must NOT read as ABI-conservative.
    let s = declared_mode_summary("str-len", &fn_ty(vec![Type::String], Type::Int)).unwrap();
    assert!(!s.is_abi_conservative(), "a Borrowed leaf refines the ABI away from Decision-24");
}
