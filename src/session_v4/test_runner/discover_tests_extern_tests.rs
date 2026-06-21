    use super::*;
    use cranelisp_types::{FQTypeName, ModuleFullPath, Scheme, Type, TypeName};
    use std::collections::HashMap;

    fn option_string() -> Type {
        Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Option")),
            vec![Type::String],
        )
    }

    fn mono_scheme(ty: Type) -> Scheme {
        Scheme { type_vars: vec![], constraints: HashMap::new(), ty }
    }

    // spec: design/arch/test-discovery.md §5 — eligibility = test- prefix AND
    // the EXACT scheme (Fn [] (Option String)).
    #[test]
    fn eligible_only_for_exact_zero_arg_option_string() {
        // The exact eligible shape.
        assert!(test_scheme_is_eligible(&mono_scheme(Type::Fn(
            vec![],
            Box::new(option_string())
        ))));
        // Wrong arity (one param) — excluded.
        assert!(!test_scheme_is_eligible(&mono_scheme(Type::Fn(
            vec![Type::Int],
            Box::new(option_string())
        ))));
        // Wrong return (Option Int) — excluded.
        assert!(!test_scheme_is_eligible(&mono_scheme(Type::Fn(
            vec![],
            Box::new(Type::ADT(
                FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Option")),
                vec![Type::Int],
            )),
        ))));
        // Not a function (a value) — excluded.
        assert!(!test_scheme_is_eligible(&mono_scheme(Type::Int)));
    }

    // spec: design/arch/test-discovery.md §6 — the wrapper closure reads its
    // captured GOT-slot address and indirects to the current code pointer.
    #[test]
    fn wrapper_indirects_through_captured_slot_and_is_late_bound() {
        // Stand up a slot (an AtomicPtr-shaped i64 cell) holding a code pointer.
        extern "C" fn test_a() -> i64 { 0 }   // None (pass)
        extern "C" fn test_b() -> i64 { 12345 } // some heap ptr sentinel

        let mut slot: i64 = test_a as *const u8 as i64;
        let slot_addr = (&raw mut slot) as i64;

        let closure = unsafe { alloc_test_wrapper_closure(slot_addr) };
        // The closure's code_ptr is the wrapper; capture[0] is the slot address.
        unsafe {
            assert_eq!(
                *((closure as *const u8).add(16) as *const i64),
                discovered_test_wrapper as *const u8 as i64
            );
            assert_eq!(*((closure as *const u8).add(32) as *const i64), slot_addr);
        }

        // Invoke the wrapper: indirects through the slot to test_a → 0.
        assert_eq!(discovered_test_wrapper(closure), 0);

        // Late binding: redefine the slot's contents (write THROUGH the slot
        // address, exactly as a redefinition's GOT store would) → the wrapper
        // runs the new body. Writing via the pointer (not the local) is also
        // what the wrapper reads, so there is no dead-store.
        unsafe { *(slot_addr as *mut i64) = test_b as *const u8 as i64; }
        assert_eq!(discovered_test_wrapper(closure), 12345);

        // Null env / null slot guard.
        assert_eq!(discovered_test_wrapper(0), 0);
    }

    // spec: design/arch/test-discovery.md §6 — null TEST_RUNNER → empty Vec.
    #[test]
    fn extern_returns_empty_vec_when_no_session() {
        // No TEST_RUNNER set on this thread.
        let v = discover_tests_extern(0);
        assert_ne!(v, 0, "should return a heap (Vec ...), even if empty");
        // len field at offset 16 must be 0.
        let len = unsafe { *((v as *const u8).add(16) as *const i64) };
        assert_eq!(len, 0);
    }
