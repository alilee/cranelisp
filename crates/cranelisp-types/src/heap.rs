use std::collections::HashMap;
use std::mem::{self, offset_of};

use crate::{Type, TypeDefInfo, TypeName};

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
    /// Accepts an optional `type_defs` registry to make authoritative decisions
    /// about ADT heap behavior based on actual constructor definitions. When
    /// `type_defs` is `None` (e.g., during early pipeline stages before type
    /// checking), ADTs conservatively classify as `Mixed`.
    ///
    /// With the registry, classification is exact:
    /// - All constructors nullary (no fields) -> `NeverHeap` (bare tags)
    /// - All constructors have fields -> `AlwaysHeap` (always heap-allocated)
    /// - Mix of nullary and data constructors -> `Mixed`
    pub fn classify(ty: &Type, type_defs: Option<&HashMap<TypeName, TypeDefInfo>>) -> HeapCategory {
        match ty {
            Type::Int | Type::Bool | Type::Float => HeapCategory::NeverHeap,
            Type::String => HeapCategory::AlwaysHeap,
            Type::Fn(_, _) => {
                // In Ring 0, functions are bare pointers (NeverHeap).
                // In Ring 1+, closures are heap-allocated.
                // Conservative: AlwaysHeap (closures are the common case after Ring 0).
                HeapCategory::AlwaysHeap
            }
            Type::ADT(name, _) => {
                Self::classify_adt(name, type_defs)
            }
            Type::Var(_) | Type::TyConApp(_, _) => {
                // Unresolved type variable: might be anything
                HeapCategory::Mixed
            }
        }
    }

    /// Classify an ADT by inspecting its constructors from the type_defs registry.
    ///
    /// Without the registry, conservatively returns `Mixed`.
    /// With the registry, counts nullary vs data constructors:
    /// - All nullary -> `NeverHeap`
    /// - All data -> `AlwaysHeap`
    /// - Mixed -> `Mixed`
    fn classify_adt(name: &TypeName, type_defs: Option<&HashMap<TypeName, TypeDefInfo>>) -> HeapCategory {
        // Vec is a built-in heap type (not registered via deftype).
        if name.as_ref() == "Vec" {
            return HeapCategory::AlwaysHeap;
        }

        let Some(registry) = type_defs else {
            // No registry available — conservative fallback
            return HeapCategory::Mixed;
        };

        let Some(info) = registry.get(name) else {
            // Unknown ADT (shouldn't happen post-typecheck, but be safe)
            return HeapCategory::Mixed;
        };

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
    use crate::{ConstructorInfo, FieldInfo, Symbol, TypeName};

    /// Helper: build a TypeDefInfo with the given constructors.
    fn make_type_def(
        name: &str,
        type_params: &[&str],
        constructors: Vec<ConstructorInfo>,
    ) -> TypeDefInfo {
        TypeDefInfo {
            name: TypeName::from(name),
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

    /// Helper: build a type_defs registry from a list of TypeDefInfos.
    fn registry(defs: Vec<TypeDefInfo>) -> HashMap<TypeName, TypeDefInfo> {
        defs.into_iter().map(|d| (d.name.clone(), d)).collect()
    }

    // --- Primitive types (no registry needed) ---

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

    // --- ADT without registry (conservative fallback) ---

    #[test]
    fn test_adt_without_registry_is_mixed() {
        let color = Type::ADT(TypeName::from("Color"), vec![]);
        assert_eq!(
            HeapCategory::classify(&color, None),
            HeapCategory::Mixed,
        );
    }

    #[test]
    fn test_parameterized_adt_without_registry_is_mixed() {
        let option_int = Type::ADT(TypeName::from("Option"), vec![Type::Int]);
        assert_eq!(
            HeapCategory::classify(&option_int, None),
            HeapCategory::Mixed,
        );
    }

    // --- ADT with registry: enum-only (all nullary) ---

    #[test]
    fn test_enum_only_adt_never_heap() {
        // (deftype Color Red Green Blue)
        let defs = registry(vec![make_type_def(
            "Color",
            &[],
            vec![
                nullary_ctor("Red", 0),
                nullary_ctor("Green", 1),
                nullary_ctor("Blue", 2),
            ],
        )]);
        let color = Type::ADT(TypeName::from("Color"), vec![]);
        assert_eq!(
            HeapCategory::classify(&color, Some(&defs)),
            HeapCategory::NeverHeap,
        );
    }

    // --- ADT with registry: all data constructors ---

    #[test]
    fn test_data_only_adt_always_heap() {
        // (deftype Wrapper [val]) — non-parameterized with data constructor
        // This is the F-2 bug case: was incorrectly NeverHeap
        let defs = registry(vec![make_type_def(
            "Wrapper",
            &[],
            vec![data_ctor("Wrapper", 0)],
        )]);
        let wrapper = Type::ADT(TypeName::from("Wrapper"), vec![]);
        assert_eq!(
            HeapCategory::classify(&wrapper, Some(&defs)),
            HeapCategory::AlwaysHeap,
        );
    }

    #[test]
    fn test_product_type_always_heap() {
        // (deftype IPoint (IPoint [:Int x :Int y])) — product type
        let defs = registry(vec![make_type_def(
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
        let point = Type::ADT(TypeName::from("IPoint"), vec![]);
        assert_eq!(
            HeapCategory::classify(&point, Some(&defs)),
            HeapCategory::AlwaysHeap,
        );
    }

    // --- ADT with registry: mixed constructors ---

    #[test]
    fn test_mixed_adt_with_registry() {
        // (deftype (Option a) None (Some [:a val]))
        let defs = registry(vec![make_type_def(
            "Option",
            &["a"],
            vec![nullary_ctor("None", 0), data_ctor("Some", 1)],
        )]);
        let option_int = Type::ADT(TypeName::from("Option"), vec![Type::Int]);
        assert_eq!(
            HeapCategory::classify(&option_int, Some(&defs)),
            HeapCategory::Mixed,
        );
    }

    // --- ADT with registry: parameterized but only nullary ---

    #[test]
    fn test_phantom_type_never_heap() {
        // (deftype (Phantom a) PhantomVal) — parameterized, but only nullary constructor
        // This was incorrectly Mixed with the old heuristic
        let defs = registry(vec![make_type_def(
            "Phantom",
            &["a"],
            vec![nullary_ctor("PhantomVal", 0)],
        )]);
        let phantom = Type::ADT(TypeName::from("Phantom"), vec![Type::Int]);
        assert_eq!(
            HeapCategory::classify(&phantom, Some(&defs)),
            HeapCategory::NeverHeap,
        );
    }

    // --- ADT with registry: unknown type (not in registry) ---

    #[test]
    fn test_unknown_adt_with_empty_registry_is_mixed() {
        let defs: HashMap<TypeName, TypeDefInfo> = HashMap::new();
        let unknown = Type::ADT(TypeName::from("Unknown"), vec![]);
        assert_eq!(
            HeapCategory::classify(&unknown, Some(&defs)),
            HeapCategory::Mixed,
        );
    }

    // --- Vec type (built-in, always heap) ---

    #[test]
    fn test_vec_always_heap_without_registry() {
        let vec_int = Type::ADT(TypeName::from("Vec"), vec![Type::Int]);
        assert_eq!(
            HeapCategory::classify(&vec_int, None),
            HeapCategory::AlwaysHeap,
        );
    }

    #[test]
    fn test_vec_always_heap_with_registry() {
        let defs: HashMap<TypeName, TypeDefInfo> = HashMap::new();
        let vec_str = Type::ADT(TypeName::from("Vec"), vec![Type::String]);
        assert_eq!(
            HeapCategory::classify(&vec_str, Some(&defs)),
            HeapCategory::AlwaysHeap,
        );
    }

    #[test]
    fn test_vec_polymorphic_always_heap() {
        let vec_var = Type::ADT(TypeName::from("Vec"), vec![Type::Var(0)]);
        assert_eq!(
            HeapCategory::classify(&vec_var, None),
            HeapCategory::AlwaysHeap,
        );
    }
}
