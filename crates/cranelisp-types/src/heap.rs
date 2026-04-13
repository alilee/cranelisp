use std::mem::{self, offset_of};

use crate::{FQTypeName, ModuleEntry, ModuleFullPath, Symbol, SymbolTable, Type, TypeDefInfo};

/// Universal header for all heap-allocated values.
/// All offsets in the compiler derive from this struct's layout.
/// Lives in cranelisp-types so both backend and runtime can reference it.
#[repr(C)]
pub struct HeapHeader {
    /// Total allocation size in bytes (header + payload). Used by dealloc.
    pub alloc_size: i64,
    /// Reference count. Accessed via atomic_rmw (Release ordering) per NFR C.4.1.
    /// Initial value: 1 (the allocating binding owns the value).
    pub rc: i64,
}

impl HeapHeader {
    pub const SIZE: usize = mem::size_of::<Self>(); // 16
    pub const ALLOC_SIZE_OFFSET: i32 = offset_of!(Self, alloc_size) as i32; // 0
    /// RC field offset — single source of truth for RC location.
    /// emit_rc_inc and emit_rc_dec use this exclusively.
    pub const RC_OFFSET: i32 = offset_of!(Self, rc) as i32; // 8
}

// Compile-time assertions — fail at build time if layout changes.
const _: () = assert!(HeapHeader::SIZE == 16);
const _: () = assert!(HeapHeader::ALLOC_SIZE_OFFSET == 0);
const _: () = assert!(HeapHeader::RC_OFFSET == 8);

/// Whether a type requires heap allocation at runtime.
/// Single source of truth -- addresses audit codegen HIGH-2.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapCategory {
    /// Never heap-allocated: Int, Bool, Float, nullary constructors
    NeverHeap,
    /// Always heap-allocated: String, closures, data constructors with fields
    AlwaysHeap,
    /// May or may not be heap: polymorphic types, some ADTs with mixed constructors
    Mixed,
}

impl HeapCategory {
    /// Classify a type's heap behavior. Single source of truth.
    ///
    /// Accepts an optional reference to the per-module symbol tables (DashMap)
    /// to make authoritative decisions about ADT heap behavior based on actual
    /// constructor definitions. When `symbol_tables` is `None` (e.g., during
    /// early pipeline stages before type checking), ADTs conservatively classify
    /// as `Mixed`.
    ///
    /// With symbol tables, classification is exact:
    /// - All constructors nullary (no fields) -> `NeverHeap` (bare tags)
    /// - All constructors have fields -> `AlwaysHeap` (always heap-allocated)
    /// - Mix of nullary and data constructors -> `Mixed`
    pub fn classify(
        ty: &Type,
        symbol_tables: Option<&dashmap::DashMap<ModuleFullPath, SymbolTable>>,
    ) -> HeapCategory {
        match ty {
            Type::Int | Type::Bool | Type::Float => HeapCategory::NeverHeap,
            Type::String => HeapCategory::AlwaysHeap,
            Type::Fn(_, _) => {
                // In Ring 0, functions are bare pointers (NeverHeap).
                // In Ring 1+, closures are heap-allocated.
                // Conservative: AlwaysHeap (closures are the common case after Ring 0).
                HeapCategory::AlwaysHeap
            }
            Type::ADT(fqtn, _) => Self::classify_adt(fqtn, symbol_tables),
            Type::Var(_) | Type::TyConApp(_, _) => {
                // Unresolved type variable: might be anything
                HeapCategory::Mixed
            }
        }
    }

    /// Classify an ADT by inspecting its constructors from the symbol tables.
    ///
    /// Without the symbol tables, conservatively returns `Mixed`.
    /// With the symbol tables, looks up `ModuleEntry::TypeDef` on the type's
    /// owning module and counts nullary vs data constructors:
    /// - All nullary -> `NeverHeap`
    /// - All data -> `AlwaysHeap`
    /// - Mixed -> `Mixed`
    fn classify_adt(
        fqtn: &FQTypeName,
        symbol_tables: Option<&dashmap::DashMap<ModuleFullPath, SymbolTable>>,
    ) -> HeapCategory {
        // Vec is a built-in heap type (not registered via deftype).
        if fqtn.name.as_ref() == "Vec" {
            return HeapCategory::AlwaysHeap;
        }

        let Some(tables) = symbol_tables else {
            // No tables available — conservative fallback
            return HeapCategory::Mixed;
        };

        // Look up the TypeDefInfo on the type's owning module.
        let Some(table) = tables.get(&fqtn.module) else {
            return HeapCategory::Mixed;
        };

        let type_key = Symbol::from(fqtn.name.as_ref());
        let info = match table.get(type_key.as_ref()) {
            Some(ModuleEntry::TypeDef { info, .. }) => info,
            _ => return HeapCategory::Mixed,
        };

        Self::classify_from_type_def_info(info)
    }

    /// Classify an ADT from its TypeDefInfo (shared logic).
    fn classify_from_type_def_info(info: &TypeDefInfo) -> HeapCategory {
        let has_nullary = info.constructors.iter().any(|c| c.fields.is_empty());
        let has_data = info.constructors.iter().any(|c| !c.fields.is_empty());

        match (has_nullary, has_data) {
            (true, true) => HeapCategory::Mixed,
            (false, true) => HeapCategory::AlwaysHeap,
            (true, false) => HeapCategory::NeverHeap,
            // No constructors at all — shouldn't happen, but treat as NeverHeap
            // (a type with no constructors can never be instantiated)
            (false, false) => HeapCategory::NeverHeap,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ConstructorInfo, FieldInfo, ModuleEntry, TypeName, Visibility};

    const TEST_MOD: &str = "test";

    /// Test helper: create an FQTypeName in a "test" module.
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from(TEST_MOD), TypeName::from(name))
    }

    /// Helper: build a TypeDefInfo with the given constructors.
    fn make_type_def(
        name: &str,
        type_params: &[&str],
        constructors: Vec<ConstructorInfo>,
    ) -> TypeDefInfo {
        TypeDefInfo {
            name: test_fqtn(name),
            type_params: type_params.iter().map(|s| Symbol::from(*s)).collect(),
            constructors,
            docstring: None,
        }
    }

    /// Helper: build a nullary constructor (no fields).
    fn nullary_ctor(name: &str, tag: usize) -> ConstructorInfo {
        ConstructorInfo {
            name: Symbol::from(name),
            tag,
            fields: vec![],
            docstring: None,
            internal: false,
        }
    }

    /// Helper: build a data constructor with one Int field.
    fn data_ctor(name: &str, tag: usize) -> ConstructorInfo {
        ConstructorInfo {
            name: Symbol::from(name),
            tag,
            fields: vec![FieldInfo {
                name: Symbol::from("val"),
                ty: Type::Int,
            }],
            docstring: None,
            internal: false,
        }
    }

    /// Helper: build a DashMap with a single module containing the given TypeDefInfos.
    fn tables_with_defs(defs: Vec<TypeDefInfo>) -> dashmap::DashMap<ModuleFullPath, SymbolTable> {
        let tables = dashmap::DashMap::new();
        let mut st = SymbolTable::new(ModuleFullPath::from(TEST_MOD));
        for def in defs {
            let key = Symbol::from(def.name.name.as_ref());
            st.insert(
                key,
                ModuleEntry::TypeDef {
                    info: def,
                    visibility: Visibility::Public,
                    constructor_scheme: None,
                    sexp: None,
                },
            );
        }
        tables.insert(ModuleFullPath::from(TEST_MOD), st);
        tables
    }

    // --- Primitive types (no tables needed) ---

    #[test]
    fn test_primitives_never_heap() {
        assert_eq!(
            HeapCategory::classify(&Type::Int, None),
            HeapCategory::NeverHeap
        );
        assert_eq!(
            HeapCategory::classify(&Type::Bool, None),
            HeapCategory::NeverHeap
        );
        assert_eq!(
            HeapCategory::classify(&Type::Float, None),
            HeapCategory::NeverHeap
        );
    }

    #[test]
    fn test_string_always_heap() {
        assert_eq!(
            HeapCategory::classify(&Type::String, None),
            HeapCategory::AlwaysHeap
        );
    }

    #[test]
    fn test_fn_always_heap() {
        let fn_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        assert_eq!(
            HeapCategory::classify(&fn_ty, None),
            HeapCategory::AlwaysHeap
        );
    }

    #[test]
    fn test_var_mixed() {
        assert_eq!(
            HeapCategory::classify(&Type::Var(0), None),
            HeapCategory::Mixed
        );
    }

    // --- ADT without tables (conservative fallback) ---

    #[test]
    fn test_adt_without_tables_is_mixed() {
        let color = Type::ADT(test_fqtn("Color"), vec![]);
        assert_eq!(
            HeapCategory::classify(&color, None),
            HeapCategory::Mixed,
        );
    }

    #[test]
    fn test_parameterized_adt_without_tables_is_mixed() {
        let option_int = Type::ADT(test_fqtn("Option"), vec![Type::Int]);
        assert_eq!(
            HeapCategory::classify(&option_int, None),
            HeapCategory::Mixed,
        );
    }

    // --- ADT with tables: enum-only (all nullary) ---

    #[test]
    fn test_enum_only_adt_never_heap() {
        // (deftype Color Red Green Blue)
        let tables = tables_with_defs(vec![make_type_def(
            "Color",
            &[],
            vec![
                nullary_ctor("Red", 0),
                nullary_ctor("Green", 1),
                nullary_ctor("Blue", 2),
            ],
        )]);
        let color = Type::ADT(test_fqtn("Color"), vec![]);
        assert_eq!(
            HeapCategory::classify(&color, Some(&tables)),
            HeapCategory::NeverHeap,
        );
    }

    // --- ADT with tables: all data constructors ---

    #[test]
    fn test_data_only_adt_always_heap() {
        // (deftype Wrapper [val]) — non-parameterized with data constructor
        // This is the F-2 bug case: was incorrectly NeverHeap
        let tables = tables_with_defs(vec![make_type_def(
            "Wrapper",
            &[],
            vec![data_ctor("Wrapper", 0)],
        )]);
        let wrapper = Type::ADT(test_fqtn("Wrapper"), vec![]);
        assert_eq!(
            HeapCategory::classify(&wrapper, Some(&tables)),
            HeapCategory::AlwaysHeap,
        );
    }

    #[test]
    fn test_product_type_always_heap() {
        // (deftype IPoint (IPoint [:Int x :Int y])) — product type
        let tables = tables_with_defs(vec![make_type_def(
            "IPoint",
            &[],
            vec![ConstructorInfo {
                name: Symbol::from("IPoint"),
                tag: 0,
                fields: vec![
                    FieldInfo {
                        name: Symbol::from("x"),
                        ty: Type::Int,
                    },
                    FieldInfo {
                        name: Symbol::from("y"),
                        ty: Type::Int,
                    },
                ],
                docstring: None,
                internal: false,
            }],
        )]);
        let point = Type::ADT(test_fqtn("IPoint"), vec![]);
        assert_eq!(
            HeapCategory::classify(&point, Some(&tables)),
            HeapCategory::AlwaysHeap,
        );
    }

    // --- ADT with tables: mixed constructors ---

    #[test]
    fn test_mixed_adt_with_tables() {
        // (deftype (Option a) None (Some [:a val]))
        let tables = tables_with_defs(vec![make_type_def(
            "Option",
            &["a"],
            vec![nullary_ctor("None", 0), data_ctor("Some", 1)],
        )]);
        let option_int = Type::ADT(test_fqtn("Option"), vec![Type::Int]);
        assert_eq!(
            HeapCategory::classify(&option_int, Some(&tables)),
            HeapCategory::Mixed,
        );
    }

    // --- ADT with tables: parameterized but only nullary ---

    #[test]
    fn test_phantom_type_never_heap() {
        // (deftype (Phantom a) PhantomVal) — parameterized, but only nullary constructor
        // This was incorrectly Mixed with the old heuristic
        let tables = tables_with_defs(vec![make_type_def(
            "Phantom",
            &["a"],
            vec![nullary_ctor("PhantomVal", 0)],
        )]);
        let phantom = Type::ADT(test_fqtn("Phantom"), vec![Type::Int]);
        assert_eq!(
            HeapCategory::classify(&phantom, Some(&tables)),
            HeapCategory::NeverHeap,
        );
    }

    // --- ADT with tables: unknown type (not in tables) ---

    #[test]
    fn test_unknown_adt_with_empty_tables_is_mixed() {
        let tables = dashmap::DashMap::new();
        let unknown = Type::ADT(test_fqtn("Unknown"), vec![]);
        assert_eq!(
            HeapCategory::classify(&unknown, Some(&tables)),
            HeapCategory::Mixed,
        );
    }

    // --- Vec type (built-in, always heap) ---

    #[test]
    fn test_vec_always_heap_without_tables() {
        let vec_int = Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
            vec![Type::Int],
        );
        assert_eq!(
            HeapCategory::classify(&vec_int, None),
            HeapCategory::AlwaysHeap,
        );
    }

    #[test]
    fn test_vec_always_heap_with_tables() {
        let tables = dashmap::DashMap::new();
        let vec_str = Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
            vec![Type::String],
        );
        assert_eq!(
            HeapCategory::classify(&vec_str, Some(&tables)),
            HeapCategory::AlwaysHeap,
        );
    }

    #[test]
    fn test_vec_polymorphic_always_heap() {
        let vec_var = Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
            vec![Type::Var(0)],
        );
        assert_eq!(
            HeapCategory::classify(&vec_var, None),
            HeapCategory::AlwaysHeap,
        );
    }
}
