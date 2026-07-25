macro_rules! primitive_declarations {
    (
        $(
            user_extern {
                name: $ename:literal,
                shim: $shim:ident($($arg:ident : $argty:ty),*) => $implementation:path, call: ($($callarg:ident),*),
                metadata: $metadata:expr,
                type_vars: $type_vars:expr,
                ownership: $ownership:expr
            }
        )*
        $(
            user_inline {
                name: $iname:literal,
                metadata: $imetadata:expr,
                type_vars: $itype_vars:expr,
                ownership: $iownership:expr
            }
        )*
        $(
            harvest_only {
                name: $hname:literal,
                shim: $hshim:ident($($harg:ident : $hargty:ty),*) => $himplementation:path, call: ($($hcallarg:ident),*)
            }
        )*
    ) => {
        $(
            #[unsafe(export_name = $ename)]
            pub(crate) extern "C" fn $shim($($arg: $argty),*) -> i64 {
                $implementation($($callarg),*)
            }
        )*
        $(
            #[unsafe(export_name = $hname)]
            pub(crate) extern "C" fn $hshim($($harg: $hargty),*) -> i64 {
                $himplementation($($hcallarg),*)
            }
        )*

        pub(crate) fn declarations() -> Vec<PrimitiveDecl> {
            let mut declarations = Vec::new();
            $(
                let metadata: PrimitiveDef = $metadata;
                assert_eq!(metadata.name.as_ref(), $ename);
                declarations.push(PrimitiveDecl::UserExtern {
                    name: $ename,
                    scheme: Box::new(Scheme {
                        type_vars: $type_vars,
                        constraints: Default::default(),
                        ty: metadata.ty,
                    }),
                    param_names: metadata.param_names,
                    docstring: metadata.docstring,
                    ownership: $ownership,
                    shim_name: stringify!($shim),
                    shim: $shim as *const u8,
                });
            )*
            $(
                let metadata: PrimitiveDef = $imetadata;
                assert_eq!(metadata.name.as_ref(), $iname);
                declarations.push(PrimitiveDecl::UserInline {
                    name: $iname,
                    scheme: Box::new(Scheme {
                        type_vars: $itype_vars,
                        constraints: Default::default(),
                        ty: metadata.ty,
                    }),
                    param_names: metadata.param_names,
                    docstring: metadata.docstring,
                    ownership: $iownership,
                });
            )*
            $(
                declarations.push(PrimitiveDecl::HarvestExtern {
                    name: $hname,
                    shim_name: stringify!($hshim),
                    shim: $hshim as *const u8,
                });
            )*
            declarations
        }
    };
}
