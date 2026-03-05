use crate::Type;

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
    /// In Ring 0, all concrete types classify as NeverHeap (no heap types exercised).
    /// The classification is correct for all types so that later rings work without changes.
    pub fn classify(ty: &Type) -> HeapCategory {
        match ty {
            Type::Int | Type::Bool | Type::Float => HeapCategory::NeverHeap,
            Type::String => HeapCategory::AlwaysHeap,
            Type::Fn(_, _) => {
                // In Ring 0, functions are bare pointers (NeverHeap).
                // In Ring 1+, closures are heap-allocated.
                // Conservative: AlwaysHeap (closures are the common case after Ring 0).
                HeapCategory::AlwaysHeap
            }
            Type::ADT(_, args) => {
                if args.is_empty() {
                    // Nullary ADT (enum-only): bare i64 tag, no heap
                    HeapCategory::NeverHeap
                } else {
                    // Parameterized ADT: may have data constructors with fields
                    HeapCategory::Mixed
                }
            }
            Type::Var(_) | Type::TyConApp(_, _) => {
                // Unresolved type variable: might be anything
                HeapCategory::Mixed
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeName;

    #[test]
    fn test_primitives_never_heap() {
        assert_eq!(HeapCategory::classify(&Type::Int), HeapCategory::NeverHeap);
        assert_eq!(HeapCategory::classify(&Type::Bool), HeapCategory::NeverHeap);
        assert_eq!(
            HeapCategory::classify(&Type::Float),
            HeapCategory::NeverHeap
        );
    }

    #[test]
    fn test_string_always_heap() {
        assert_eq!(
            HeapCategory::classify(&Type::String),
            HeapCategory::AlwaysHeap
        );
    }

    #[test]
    fn test_nullary_adt_never_heap() {
        let color = Type::ADT(TypeName::from("Color"), vec![]);
        assert_eq!(HeapCategory::classify(&color), HeapCategory::NeverHeap);
    }

    #[test]
    fn test_parameterized_adt_mixed() {
        let option_int = Type::ADT(TypeName::from("Option"), vec![Type::Int]);
        assert_eq!(HeapCategory::classify(&option_int), HeapCategory::Mixed);
    }

    #[test]
    fn test_var_mixed() {
        assert_eq!(HeapCategory::classify(&Type::Var(0)), HeapCategory::Mixed);
    }
}
