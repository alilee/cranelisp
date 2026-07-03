    use super::*;

    #[test]
    fn primitives_table_contains_ring0_entries() {
        // Every Ring 0 primitive name must appear as a `ModuleEntry::Def`.
        for prim in ring0_primitives() {
            assert!(
                PRIMITIVES_TABLE.get(prim.name.as_ref()).is_some(),
                "missing entry for {}",
                prim.name
            );
        }
    }

    #[test]
    fn primitives_table_contains_ring1_entries() {
        for prim in ring1_primitives() {
            assert!(
                PRIMITIVES_TABLE.get(prim.name.as_ref()).is_some(),
                "missing entry for {}",
                prim.name
            );
        }
    }

    #[test]
    fn primitives_table_contains_ring3_entries() {
        for prim in ring3_primitives() {
            assert!(
                PRIMITIVES_TABLE.get(prim.name.as_ref()).is_some(),
                "missing entry for {}",
                prim.name
            );
        }
    }

    #[test]
    fn primitives_table_contains_vec_query_family() {
        // All four Vec-query primitives must resolve by name (FIXME 0277 — the
        // production prelude's stdlib/collections/vec.cl uses vec-get/vec-set/
        // vec-push/vec-len; only vec-len was previously present).
        for name in ["vec-get", "vec-set", "vec-push", "vec-len"] {
            assert!(
                PRIMITIVES_TABLE.get(name).is_some(),
                "missing Vec-query primitive {name}"
            );
        }
    }

    #[test]
    fn primitives_table_is_non_empty_with_expected_minimum() {
        // ring0 (20) + ring1 (~17) + ring3 (1) + vec-query (4) = ~42.
        // Hold the floor at 30 to absorb small registry churn without
        // requiring this test to track an exact count.
        assert!(
            PRIMITIVES_TABLE.symbols.len() >= 30,
            "expected at least 30 entries, got {}",
            PRIMITIVES_TABLE.symbols.len(),
        );
    }

    #[test]
    fn every_entry_is_a_callable_target() {
        // FIXME-0476 consumption (S102 CS-B1-be): the invariant is
        // *callability*, not slot-presence. Every primitives-table entry is a
        // dispatchable call target — either slot-dispatched (`Extern`) or
        // inline-dispatched (`Inline`). Post-cure the vec trio carries
        // `PrimitiveBody::Inline` with NO slot, so the old
        // `callable_got_slot().is_some()` assertion no longer holds for every
        // entry; `is_callable_target()` is the right predicate (it covers both
        // arms). This is the exact stop-predicate the backend's resolution
        // walks now use.
        for (name, entry) in PRIMITIVES_TABLE.symbols.iter() {
            let ModuleEntry::Def { .. } = entry else {
                panic!("entry {name} should be a Def");
            };
            assert!(
                entry.is_callable_target(),
                "entry {name} is not a callable target"
            );
        }
    }

    #[test]
    fn vec_trio_is_inline_no_slot_and_vec_len_is_extern() {
        // FIXME-0476 consumption (S102 CS-B1-be): the representation cure. The
        // three inline-only vec ops carry `PrimitiveBody::Inline` and answer
        // `callable_got_slot() == None` **by construction** — no
        // allocated-but-NULL phantom slot is ever constructed (the third
        // phantom-slot instance is now unrepresentable, Principle 20). `vec-len`
        // is the sole `Extern` member: it has a real shim and a populated slot.
        for name in ["vec-get", "vec-set", "vec-push"] {
            let entry = PRIMITIVES_TABLE
                .get(name)
                .unwrap_or_else(|| panic!("missing {name}"));
            let ModuleEntry::Def { kind, .. } = entry else {
                panic!("entry {name} should be a Def");
            };
            assert!(
                matches!(**kind, DefKind::Primitive { body: PrimitiveBody::Inline, .. }),
                "entry {name} must be PrimitiveBody::Inline; got {kind:?}"
            );
            assert!(
                entry.callable_got_slot().is_none(),
                "inline {name} must carry NO got_slot (no phantom NULL slot)"
            );
            assert!(
                entry.is_callable_target(),
                "inline {name} must still be a callable target (name-resolution stop)"
            );
        }

        let vec_len = PRIMITIVES_TABLE.get("vec-len").expect("missing vec-len");
        let ModuleEntry::Def { kind, .. } = vec_len else {
            panic!("vec-len should be a Def");
        };
        assert!(
            matches!(**kind, DefKind::Primitive { body: PrimitiveBody::Extern { .. }, .. }),
            "vec-len must be PrimitiveBody::Extern; got {kind:?}"
        );
        let slot = vec_len
            .callable_got_slot()
            .expect("vec-len must carry a populated got_slot");
        assert!(
            !PRIMITIVES_TABLE.got.load_slot(slot).is_null(),
            "vec-len GOT slot must hold its extern shim address"
        );
    }

    #[test]
    fn every_entry_is_def_kind_primitive() {
        // Decision 0048 (A2 reversed, FIXME 0244, 2026-05-31) — primitive-ness
        // is read from `kind: DefKind::Primitive` (the canonical fact), NOT
        // from `code`. Every entry carries the payload-free `DefKind::Primitive`
        // unit variant, and `code: None` (the `ModuleEntry::def(..).build()`
        // builder default; there is no `Code::Primitive` marker). The GOT
        // remains the single source of truth for the `*const u8` (Decision 35).
        for (name, entry) in PRIMITIVES_TABLE.symbols.iter() {
            let ModuleEntry::Def { kind, code, .. } = entry else {
                panic!("entry {name} should be a Def");
            };
            assert!(
                matches!(**kind, DefKind::Primitive { .. }),
                "entry {name} must carry DefKind::Primitive; got {kind:?}"
            );
            // Belt-and-suspenders: `code` is the builder default `None`
            // (no spec contract — `kind` is authoritative).
            assert!(
                code.is_none(),
                "entry {name} must carry code: None; got {code:?}"
            );
        }
    }

    #[test]
    fn got_slots_hold_extern_ptrs_for_harvested_shims() {
        // For each entry whose name appears in the shim harvest, the GOT
        // slot must hold the matching fn pointer.
        let shims = extern_shims();
        for (name, entry) in PRIMITIVES_TABLE.symbols.iter() {
            // Inline-dispatched primitives (the vec trio, FIXME 0476) carry no
            // slot and no shim by construction — skip them; only slot-carrying
            // Extern entries have a GOT address to check.
            let Some(slot) = entry.callable_got_slot() else {
                continue;
            };
            let stored = PRIMITIVES_TABLE.got.load_slot(slot);
            if let Some(expected) = shims.get(name.as_ref()) {
                assert_eq!(
                    stored, *expected,
                    "GOT slot {slot} for {name} does not match shim address"
                );
                assert!(!stored.is_null(), "GOT slot {slot} for {name} is null");
            }
        }
    }

    // -----------------------------------------------------------------------
    // Content harness (deliverable C(a)) — assert the spec contract
    // (`spec/appendix-a-builtins.md` §A.2/§A.3/§A.5) against each inserted
    // table entry. Parity-iterate the `ring{0,1,3}_primitives()` builders
    // (the constructor input) so the harness checks the insert path round-trips
    // builder input → table output, plus an explicit `vec-len` row.
    // -----------------------------------------------------------------------

    /// Assert one inserted entry against its expected `(ty, param_names)`.
    fn assert_content_row(name: &str, expected_ty: &cranelisp_types::Type, expected_params: &[&str]) {
        let entry = PRIMITIVES_TABLE
            .get(name)
            .unwrap_or_else(|| panic!("missing PRIMITIVES_TABLE entry for {name}"));
        let ModuleEntry::Def {
            scheme,
            param_names,
            kind,
            ..
        } = entry
        else {
            panic!("entry {name} should be a Def");
        };
        // scheme.ty is the boundary Type::Fn per spec §A.3.
        assert_eq!(&scheme.ty, expected_ty, "scheme.ty mismatch for {name}");
        // param_names match the spec contract.
        let actual: Vec<&str> = param_names.iter().map(|p| p.as_ref()).collect();
        assert_eq!(actual.as_slice(), expected_params, "param_names mismatch for {name}");
        // The entry is a dispatchable callable target — either slot-dispatched
        // (`Extern`) or inline-dispatched (`Inline`, the vec trio; FIXME 0476).
        // `is_callable_target()` covers both arms (the old
        // `callable_got_slot().is_some()` excluded the slot-less inline trio).
        assert!(entry.is_callable_target(), "entry {name} not a callable target");
        // kind is the primitive discriminator.
        assert!(matches!(**kind, DefKind::Primitive { .. }), "entry {name} kind != Primitive");
        // jit_name IS the symbol-table key (S69 Submission 36) — pinned by the
        // successful `.get(name)` lookup above.
    }

    #[test]
    fn content_harness_ring_builders_round_trip() {
        // Parity check: every `PrimitiveDef` from the three ring builders
        // round-trips through the inserted `ModuleEntry::Def` — its
        // (name, ty, param_names) match the table entry. Catches insert-path
        // regressions (the builder is the source of the spec contract).
        let mut count = 0usize;
        for prim in ring0_primitives()
            .into_iter()
            .chain(ring1_primitives())
            .chain(ring3_primitives())
        {
            let params: Vec<&str> = prim.param_names.iter().map(|p| p.as_ref()).collect();
            assert_content_row(prim.name.as_ref(), &prim.ty, &params);
            count += 1;
        }
        // Sanity: the union is non-trivial (guards against an empty iterator
        // silently passing the loop).
        assert!(count >= 30, "expected >=30 ring-builder rows, got {count}");
    }

    #[test]
    fn content_harness_vec_query_rows() {
        use cranelisp_types::{ModuleFullPath, Type, TypeName};
        // The Vec-query family is not in any ring builder — explicit rows.
        // Each carries the POLYMORPHIC appendix-A §A.3 scheme over a single
        // quantified element var `a` (TypeId 0 here; remapped on instantiate).
        // A boundary-erased monomorphic scheme (`(Fn [Int] …)`) fails to unify
        // against a `(Vec a)` argument at the call site — see FIXME 0277.
        let vec_a = || {
            Type::adt(
                ModuleFullPath::from("primitives"),
                TypeName::from("Vec"),
                vec![Type::Var(0)],
            )
        };
        // vec-get :: forall a. (Fn [(Vec a) Int] a)
        assert_content_row(
            "vec-get",
            &Type::Fn(vec![vec_a(), Type::Int], Box::new(Type::Var(0))),
            &["v", "idx"],
        );
        // vec-set :: forall a. (Fn [(Vec a) Int a] (Vec a))
        assert_content_row(
            "vec-set",
            &Type::Fn(vec![vec_a(), Type::Int, Type::Var(0)], Box::new(vec_a())),
            &["v", "idx", "val"],
        );
        // vec-push :: forall a. (Fn [(Vec a) a] (Vec a))
        assert_content_row(
            "vec-push",
            &Type::Fn(vec![vec_a(), Type::Var(0)], Box::new(vec_a())),
            &["v", "val"],
        );
        // vec-len :: forall a. (Fn [(Vec a)] Int)
        assert_content_row(
            "vec-len",
            &Type::Fn(vec![vec_a()], Box::new(Type::Int)),
            &["v"],
        );
    }

    // -----------------------------------------------------------------------
    // Behavioural harness (deliverable C(b)) — transmute-and-invoke the 20
    // PURE scalar ops (ring0 i64/f64 arithmetic+comparison, eq-bool, not)
    // against known I/O pairs. Heap/allocator-coupled ops are EXCLUDED (they
    // stay e2e / in string.rs + vec.rs module-local tests).
    // -----------------------------------------------------------------------

    /// Load the GOT-slot fn ptr for a primitive, asserting it is populated.
    fn slot_ptr(name: &str) -> *const u8 {
        let entry = PRIMITIVES_TABLE
            .get(name)
            .unwrap_or_else(|| panic!("missing entry for {name}"));
        let Some(slot) = entry.callable_got_slot() else {
            panic!("{name} must be a Def with got_slot");
        };
        let ptr = PRIMITIVES_TABLE.got.load_slot(slot);
        assert!(!ptr.is_null(), "GOT slot for {name} is null");
        ptr
    }

    /// Invoke an `(i64, i64) -> i64` primitive by name.
    fn call_i64_i64(name: &str, a: i64, b: i64) -> i64 {
        // SAFETY: ptr is loaded from the GOT slot populated by extern_shims()
        // with the matching `extern "C" fn(i64, i64) -> i64`; we transmute back.
        let f: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(slot_ptr(name)) };
        f(a, b)
    }

    /// Invoke a `(i64) -> i64` primitive by name.
    fn call_i64(name: &str, a: i64) -> i64 {
        // SAFETY: as above, for `extern "C" fn(i64) -> i64`.
        let f: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(slot_ptr(name)) };
        f(a)
    }

    /// Invoke an `(f64, f64) -> f64` primitive by name (f64-bits ABI, Decision 10).
    fn call_f64_f64(name: &str, a: f64, b: f64) -> f64 {
        f64::from_bits(call_i64_i64(name, a.to_bits() as i64, b.to_bits() as i64) as u64)
    }

    /// Invoke an `(f64, f64) -> i64` comparison primitive (0/1).
    fn call_f64_cmp(name: &str, a: f64, b: f64) -> i64 {
        call_i64_i64(name, a.to_bits() as i64, b.to_bits() as i64)
    }

    #[test]
    fn behavioural_ring0_int_arithmetic() {
        // spec: appendix-a-builtins §A.2 — int arithmetic.
        assert_eq!(call_i64_i64("add-i64", 2, 3), 5);
        assert_eq!(call_i64_i64("sub-i64", 7, 4), 3);
        assert_eq!(call_i64_i64("mul-i64", 6, 7), 42);
        // div-i64: only the non-zero happy path here (div-by-zero panic path
        // is e2e — couples to the intrinsics thread-local error slot).
        assert_eq!(call_i64_i64("div-i64", 6, 2), 3);
    }

    #[test]
    fn behavioural_ring0_int_comparison() {
        // spec: appendix-a-builtins §A.2 — int comparison (0/1).
        assert_eq!(call_i64_i64("eq-i64", 3, 3), 1);
        assert_eq!(call_i64_i64("eq-i64", 3, 4), 0);
        assert_eq!(call_i64_i64("lt-i64", 2, 3), 1);
        assert_eq!(call_i64_i64("lt-i64", 3, 2), 0);
        assert_eq!(call_i64_i64("gt-i64", 3, 2), 1);
        assert_eq!(call_i64_i64("gt-i64", 2, 3), 0);
        assert_eq!(call_i64_i64("le-i64", 3, 3), 1);
        assert_eq!(call_i64_i64("le-i64", 4, 3), 0);
        assert_eq!(call_i64_i64("ge-i64", 3, 3), 1);
        assert_eq!(call_i64_i64("ge-i64", 2, 3), 0);
    }

    #[test]
    fn behavioural_ring0_float_arithmetic() {
        // spec: appendix-a-builtins §A.2 — float arithmetic (f64-bits ABI).
        assert_eq!(call_f64_f64("add-f64", 1.5, 2.5), 4.0);
        assert_eq!(call_f64_f64("sub-f64", 5.0, 1.5), 3.5);
        assert_eq!(call_f64_f64("mul-f64", 2.0, 3.5), 7.0);
        assert_eq!(call_f64_f64("div-f64", 9.0, 3.0), 3.0);
    }

    #[test]
    fn behavioural_ring0_float_comparison() {
        // spec: appendix-a-builtins §A.2 — float comparison (0/1).
        assert_eq!(call_f64_cmp("eq-f64", 1.5, 1.5), 1);
        assert_eq!(call_f64_cmp("eq-f64", 1.5, 2.5), 0);
        assert_eq!(call_f64_cmp("lt-f64", 1.0, 2.0), 1);
        assert_eq!(call_f64_cmp("lt-f64", 2.0, 1.0), 0);
        assert_eq!(call_f64_cmp("gt-f64", 2.0, 1.0), 1);
        assert_eq!(call_f64_cmp("gt-f64", 1.0, 2.0), 0);
        assert_eq!(call_f64_cmp("le-f64", 1.5, 1.5), 1);
        assert_eq!(call_f64_cmp("le-f64", 2.0, 1.5), 0);
        assert_eq!(call_f64_cmp("ge-f64", 1.5, 1.5), 1);
        assert_eq!(call_f64_cmp("ge-f64", 1.0, 1.5), 0);
    }

    #[test]
    fn behavioural_ring0_boolean() {
        // spec: appendix-a-builtins §A.3 — not (Decision 0048 C1) + eq-bool.
        assert_eq!(call_i64("not", 0), 1, "(not false) = true");
        assert_eq!(call_i64("not", 1), 0, "(not true) = false");
        assert_eq!(call_i64_i64("eq-bool", 1, 1), 1);
        assert_eq!(call_i64_i64("eq-bool", 1, 0), 0);
    }

    // -----------------------------------------------------------------------
    // Bitwise integer operations (FIXME 0416, S91). The fallback GOT shims
    // (`ring0::bit_and` … `ring0::popcount`) back the mappable/by-value and
    // `--link` paths; these behavioural tests drive them through the GOT slot
    // exactly as the arithmetic ops above. The inline-CLIF path is unit-tested
    // separately in `cranelisp-backend::primitives_inline::tests`.
    // -----------------------------------------------------------------------

    #[test]
    fn behavioural_ring0_bitwise() {
        // spec: appendix-a-builtins §A.3 — binary bitwise + shifts.
        assert_eq!(call_i64_i64("bit-and", 12, 10), 8);
        assert_eq!(call_i64_i64("bit-or", 12, 10), 14);
        assert_eq!(call_i64_i64("bit-xor", 12, 10), 6);
        assert_eq!(call_i64_i64("shl", 1, 4), 16);
        assert_eq!(call_i64_i64("shr", 16, 2), 4);
        // Arithmetic right shift: the sign bit replicates (NOT logical).
        assert_eq!(call_i64_i64("shr", -8, 1), -4);
        assert_eq!(call_i64_i64("shr", -1, 63), -1);
        // Shift count masked mod 64 (matches the inline Cranelift path).
        assert_eq!(call_i64_i64("shl", 1, 64), 1);
        assert_eq!(call_i64_i64("shr", 256, 64), 256);
        assert_eq!(call_i64_i64("shl", 1, 65), 2);
    }

    #[test]
    fn behavioural_ring0_bitwise_unary() {
        // spec: appendix-a-builtins §A.3 — bit-not (full 64-bit) + popcount.
        assert_eq!(call_i64("bit-not", 0), -1);
        assert_eq!(call_i64("bit-not", 5), -6);
        assert_eq!(call_i64("bit-not", -1), 0);
        assert_eq!(call_i64("popcount", 0), 0);
        assert_eq!(call_i64("popcount", 7), 3);
        assert_eq!(call_i64("popcount", -1), 64);
    }

    #[test]
    fn registration_parity_bitwise_ops() {
        // spec: appendix-a-builtins §A.3 — each new bitwise primitive registers
        // identically to `add-i64`: a `DefKind::Primitive` entry with a
        // populated GOT slot and the right `(Fn …)` scheme. Mirrors the
        // `content_harness_*` / `add-i64` assertions above.
        use cranelisp_types::Type;
        let int_int_int = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
        let int_int = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        assert_content_row("bit-and", &int_int_int, &["lhs", "rhs"]);
        assert_content_row("bit-or", &int_int_int, &["lhs", "rhs"]);
        assert_content_row("bit-xor", &int_int_int, &["lhs", "rhs"]);
        assert_content_row("shl", &int_int_int, &["v", "amt"]);
        assert_content_row("shr", &int_int_int, &["v", "amt"]);
        assert_content_row("bit-not", &int_int, &["x"]);
        assert_content_row("popcount", &int_int, &["x"]);

        // Each GOT slot holds its harvested extern shim address (mappable /
        // `--link` resolution), exactly as `add-i64`'s slot does.
        let shims = extern_shims();
        for name in [
            "bit-and", "bit-or", "bit-xor", "bit-not", "shl", "shr", "popcount",
        ] {
            let entry = PRIMITIVES_TABLE.get(name).unwrap();
            let slot = entry.callable_got_slot().unwrap();
            let stored = PRIMITIVES_TABLE.got.load_slot(slot);
            assert!(!stored.is_null(), "GOT slot for {name} is null");
            assert_eq!(
                stored,
                *shims.get(name).unwrap(),
                "GOT slot for {name} must hold its extern shim address"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Static-backing harness (FIXME 0280) — the primitives GOT is constructed
    // over the exported `__cranelisp_got_primitives` static slab, not a heap
    // allocation, so it is addressable as a link-time symbol in `--link` mode.
    // -----------------------------------------------------------------------

    #[test]
    fn primitives_got_base_is_the_exported_static_slab() {
        // The table's GOT base_ptr() must point AT the exported static slab.
        // This is the invariant that makes `__cranelisp_got_primitives` a valid
        // link-time symbol: the symbol's address (the slab) is the same address
        // backend-emitted GOT-indirect dispatch reads at runtime.
        let slab_addr = PRIMITIVES_GOT_SLAB.as_ptr() as *const u8;
        assert_eq!(
            PRIMITIVES_TABLE.got.base_ptr(),
            slab_addr,
            "primitives GOT must be backed by the exported static slab"
        );
    }

    #[test]
    fn static_slab_slots_populated_after_force() {
        // Forcing the LazyLock populates the slab's slots with the harvested
        // extern fn addresses. Read them directly off the static slab (not via
        // the table API) to prove the writes land in the exported memory that
        // `--link` binaries address.
        LazyLock::force(&PRIMITIVES_TABLE);
        let entry = PRIMITIVES_TABLE
            .get("add-i64")
            .expect("add-i64 must be present");
        let Some(slot) = entry.callable_got_slot() else {
            panic!("add-i64 must be a Def with got_slot");
        };
        let via_slab =
            PRIMITIVES_GOT_SLAB[slot].load(std::sync::atomic::Ordering::Acquire) as *const u8;
        assert!(
            !via_slab.is_null(),
            "static slab slot {slot} for add-i64 must hold the extern fn ptr after force"
        );
        assert_eq!(
            via_slab,
            ring0::add_i64 as *const u8,
            "static slab slot must hold add-i64's address"
        );
    }

    // -----------------------------------------------------------------------
    // Docstring harness (FIXME 0308) — every primitive's `ModuleEntry::Def`
    // carries a non-empty `docstring` (the §A.5 MUST Description text), wired
    // via `.docstring(prim.docstring)` in `insert_primitive_entry` /
    // `insert_vec_query_entries`. `int` reads it through the symbol table for
    // the `; classification - docstring` REPL suffix.
    // -----------------------------------------------------------------------

    #[test]
    fn every_primitive_has_a_docstring() {
        // spec: appendix-a-builtins §A.5 — every primitive MUST carry its
        // Description text. Guards against a new primitive being added without
        // wiring its docstring (the field would be `None` or empty).
        for (name, entry) in PRIMITIVES_TABLE.symbols.iter() {
            let ModuleEntry::Def { docstring, .. } = entry else {
                panic!("entry {name} should be a Def");
            };
            let doc = docstring
                .as_deref()
                .unwrap_or_else(|| panic!("entry {name} has no docstring (None)"));
            assert!(
                !doc.trim().is_empty(),
                "entry {name} has an empty docstring"
            );
        }
    }

    #[test]
    fn docstring_spot_check_pins_expected_text() {
        // spec: appendix-a-builtins §A.5 — pin that the wiring carries the
        // RIGHT string, not just any non-empty string. `add-i64` flows from
        // `ring0_primitives()` (operator.rs); `vec-len` flows from the
        // `insert_vec_query_entries` hand-built rows (lib.rs).
        let expect = |name: &str, want: &str| {
            let entry = PRIMITIVES_TABLE
                .get(name)
                .unwrap_or_else(|| panic!("missing entry for {name}"));
            let ModuleEntry::Def { docstring, .. } = entry else {
                panic!("entry {name} should be a Def");
            };
            assert_eq!(
                docstring.as_deref(),
                Some(want),
                "docstring mismatch for {name}"
            );
        };
        expect("add-i64", "Add");
        expect("vec-len", "Number of elements");
    }

    #[test]
    fn extern_shims_harvest_covers_full_inventory() {
        // Sanity check on the extern_shims() harvest: every shim name must
        // be present as a primitives entry OR be one of the known
        // out-of-table extern shims (reachable via the harvest for GOT
        // population from other modules, but not registered in
        // `PRIMITIVES_TABLE` itself):
        //
        // - `neq-i64` / `neq-f64` / `neq-bool` / `neq-string` — reachable
        //   through trait-method resolution (`Eq.!=`), not surfaced as
        //   entries in the typecheck-side `ring0_primitives()` table.
        // - `sconcat` — registered in the synthetic `macros` module per
        //   `spec/09-macros.md`, not in `primitives`.
        for name in extern_shims().keys() {
            assert!(
                PRIMITIVES_TABLE.get(name).is_some()
                    || matches!(
                        *name,
                        "neq-i64" | "neq-f64" | "neq-bool" | "neq-string" | "sconcat"
                    ),
                "shim {name} has no PRIMITIVES_TABLE entry"
            );
        }
    }
