mod abi_facts {
    #[derive(Clone, Copy)]
    pub(crate) enum AbiKind {
        Scalar,
        OwnedHandle,
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

    impl AbiHandle for super::Owned {
        const KIND: AbiKind = AbiKind::OwnedHandle;

        unsafe fn from_abi(raw: i64) -> Self {
            super::Owned(raw)
        }

        fn into_abi(self) -> i64 {
            self.0
        }
    }
}

struct Owned(i64);

struct Borrowed<'a>(i64, std::marker::PhantomData<&'a ()>);

fn body_borrows(value: Borrowed<'static>) -> Owned {
    Owned(value.0)
}

struct Symbol(&'static str);

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.0
    }
}

struct PrimitiveDef {
    name: Symbol,
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
        name: "borrowed-shim-token",
        shim: shim_borrowed_token(value: Borrowed<'static>) -> Owned => body_borrows, call: (value),
        metadata: PrimitiveDef {
            name: Symbol("borrowed-shim-token"),
            ty: (),
            param_names: vec!["value".to_owned()],
            docstring: "compile-fail fixture",
        },
        type_vars: vec![],
        ownership: ()
    }
}

fn main() {}
