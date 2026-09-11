mod abi_facts {
    #[derive(Clone, Copy)]
    pub(crate) enum AbiKind {
        Scalar,
    }

    pub(crate) trait AbiHandle: Sized {
        const KIND: AbiKind;
        unsafe fn from_abi(raw: i64) -> Self;
        fn into_abi(self) -> i64;
    }

    impl AbiHandle for i64 {
        const KIND: AbiKind = AbiKind::Scalar;

        unsafe fn from_abi(raw: i64) -> Self {
            raw
        }

        fn into_abi(self) -> i64 {
            self
        }
    }
}

struct Owned(i64);

fn body_requires_owner(value: Owned) -> i64 {
    value.0
}

struct PrimitiveDef {
    name: String,
    ty: (),
    param_names: Vec<String>,
    docstring: &'static str,
}

struct Scheme {
    type_vars: Vec<()>,
    constraints: (),
    ty: (),
}

enum PrimitiveDecl {
    UserExtern {
        name: &'static str,
        scheme: Box<Scheme>,
        param_names: Vec<String>,
        docstring: &'static str,
        ownership: (),
        shim_name: &'static str,
        shim: *const u8,
        abi_param_kinds: Vec<abi_facts::AbiKind>,
        abi_result_kind: abi_facts::AbiKind,
    },
}

include!("../../declaration_macro.rs");

primitive_declarations! {
    user_extern {
        name: "typed-shim-body-mismatch",
        shim: shim_typed_mismatch(value: i64) -> i64 => body_requires_owner, call: (value),
        metadata: PrimitiveDef {
            name: "typed-shim-body-mismatch".to_owned(),
            ty: (),
            param_names: vec!["value".to_owned()],
            docstring: "compile-fail fixture",
        },
        type_vars: vec![],
        ownership: ()
    }
}

fn main() {}
