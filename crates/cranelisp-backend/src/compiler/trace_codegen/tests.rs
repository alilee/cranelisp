use super::*;
use cranelisp_intrinsics::handle::Owned;
use cranelisp_intrinsics::heap_string::{alloc_string, read_string_as_str};
use cranelisp_intrinsics::trace::{
    consume_trace_call, cranelisp_collect_trace, cranelisp_trace_format,
    cranelisp_trace_restore_got, cranelisp_trace_swap_got,
};
use cranelisp_types::{
    CallableArmDraft, CallableOrigin, ConcreteType, DefnVariant, Expr, ModuleFullPath,
    MonoDefnVariant, MonoExpr, Realization, Scheme, Span, Symbol, SymbolTable, TemplateBody,
    TemplateKind, Type, Visibility,
};
use dashmap::DashMap;
use std::collections::HashMap;

// ── Descriptor-bake round-trip against the intrinsics walker ──────────────
//
// These build descriptor blobs with the SAME `DescriptorBlob` primitives the
// production bakers (`bake_descriptor` / `bake_vec` / `bake_adt`) use, then
// exercise the intrinsics-owned `cranelisp_trace_format` against them. A pass
// proves the arena encoding backend emits is read correctly by the formatter
// — the cross-crate ABI is in agreement (FIXME 0254 + 0255).

/// Run `cranelisp_trace_format` on a baked blob root and read back the result.
///
/// The formatter renders only on the thread that records a trace (packet row
/// D8), so the call holds the trace role, taken and released through the
/// entries a trace form calls: a swap of a GOT buffer this test owns with no
/// slot wrapped, then restore and collect.
fn fmt(value: i64, blob: &DescriptorBlob, root: usize) -> String {
    let mut got = vec![0i64; cranelisp_types::GOT_TABLE_SIZE];
    let got_base = got.as_mut_ptr() as i64;
    let no_slots = std::ptr::NonNull::<u32>::dangling().as_ptr() as i64;
    let no_wrappers = std::ptr::NonNull::<i64>::dangling().as_ptr() as i64;
    let saved = cranelisp_trace_swap_got(got_base, 0, no_slots, no_wrappers);
    let ptr = unsafe { blob.buf.as_ptr().add(root) } as i64;
    let s_heap = cranelisp_trace_format(value, ptr);
    assert_ne!(
        s_heap, 0,
        "the recording thread receives a formatted String"
    );
    let rendered = unsafe { read_string_as_str(s_heap) }.to_string();
    cranelisp_trace_restore_got(got_base, saved);
    consume_trace_call(unsafe { Owned::from_abi(cranelisp_collect_trace()) });
    rendered
}

#[test]
fn bake_int_descriptor_round_trips() {
    let mut b = DescriptorBlob::new();
    let d = b.reserve_desc();
    b.set_kind(d, DescriptorKind::Int);
    assert_eq!(fmt(42, &b, d), "42");
    assert_eq!(fmt(-7, &b, d), "-7");
}

#[test]
fn bake_bool_float_string_descriptors_round_trip() {
    let mut b = DescriptorBlob::new();
    let bd = b.reserve_desc();
    b.set_kind(bd, DescriptorKind::Bool);
    let fd = b.reserve_desc();
    b.set_kind(fd, DescriptorKind::Float);
    let sd = b.reserve_desc();
    b.set_kind(sd, DescriptorKind::String);
    assert_eq!(fmt(1, &b, bd), "true");
    assert_eq!(fmt(0, &b, bd), "false");
    assert_eq!(fmt(1.0_f64.to_bits() as i64, &b, fd), "1.0");
    let heap = alloc_string(b"hi") as i64;
    assert_eq!(fmt(heap, &b, sd), "\"hi\"");
}

#[test]
fn bake_vec_of_int_descriptor_round_trips() {
    // Mirror `bake_vec`: root(Vec) with child0_off → child(Int).
    let mut b = DescriptorBlob::new();
    let root = b.reserve_desc();
    b.set_kind(root, DescriptorKind::Vec);
    let child = b.reserve_desc();
    b.set_kind(child, DescriptorKind::Int);
    b.set_self_rel(root + OFF_CHILD0, child);

    let v = cranelisp_intrinsics::vec_runtime::vec_new(3);
    let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 10);
    let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 20);
    let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 30);
    assert_eq!(fmt(v, &b, root), "[10 20 30]");
}

/// Build an `(Option a)` instantiated at `Int` blob by hand, mirroring the
/// exact record/ctor-table layout `bake_adt` emits, then round-trip
/// `(Some 42)` + `None` through the walker. Exercises the polymorphic-field
/// concrete-substitution outcome (Int field descriptor baked from `a := Int`)
/// and the nested data path.
#[test]
fn bake_polymorphic_adt_concrete_substitution_round_trips() {
    let mut b = DescriptorBlob::new();
    let root = b.reserve_desc();
    b.set_kind(root, DescriptorKind::Adt);
    // Some's single field, substituted a := Int.
    let int_field = b.reserve_desc();
    b.set_kind(int_field, DescriptorKind::Int);

    let type_name = b.append_str("Option");
    let none_name = b.append_str("None");
    let some_name = b.append_str("Some");
    // fields_off array for Some (1 self-rel i32 → int_field).
    b.align4();
    let some_fields = b.pos();
    b.buf.extend_from_slice(&0i32.to_le_bytes());
    b.set_self_rel(some_fields, int_field);

    // CtorTable [n=2 | single_match=0 | 2 entries].
    b.align4();
    let ctab = b.pos();
    b.buf.extend_from_slice(&2i32.to_le_bytes());
    b.buf.extend_from_slice(&0i32.to_le_bytes());
    let entries_at = b.pos();
    b.buf.extend_from_slice(&[0u8; 2 * 16]);
    // None tag=0 n_fields=0.
    b.write_i32(entries_at, 0);
    b.write_i32(entries_at + 4, 0);
    b.set_self_rel(entries_at + 8, none_name);
    b.write_i32(entries_at + 12, 0);
    // Some tag=1 n_fields=1.
    b.write_i32(entries_at + 16, 1);
    b.write_i32(entries_at + 16 + 4, 1);
    b.set_self_rel(entries_at + 16 + 8, some_name);
    b.set_self_rel(entries_at + 16 + 12, some_fields);

    b.set_self_rel(root + OFF_NAME, type_name);
    b.set_self_rel(root + OFF_CTORS, ctab);

    assert_eq!(fmt(0, &b, root), "Option.None");
    let some_val = alloc_adt_for_test(1, &[42]);
    assert_eq!(fmt(some_val, &b, root), "(Option.Some 42)");
}

/// Nested ADT: `(Option (Vec Int))` rendering `(Some [1 2])`. Exercises a
/// field child descriptor that is itself a Vec-of-Int (two levels of nesting
/// through the self-relative offsets).
#[test]
fn bake_nested_adt_round_trips() {
    let mut b = DescriptorBlob::new();
    let root = b.reserve_desc();
    b.set_kind(root, DescriptorKind::Adt);
    // Some's field is (Vec Int): Vec root + Int child.
    let vec_field = b.reserve_desc();
    b.set_kind(vec_field, DescriptorKind::Vec);
    let int_child = b.reserve_desc();
    b.set_kind(int_child, DescriptorKind::Int);
    b.set_self_rel(vec_field + OFF_CHILD0, int_child);

    let type_name = b.append_str("Option");
    let some_name = b.append_str("Some");
    b.align4();
    let some_fields = b.pos();
    b.buf.extend_from_slice(&0i32.to_le_bytes());
    b.set_self_rel(some_fields, vec_field);

    b.align4();
    let ctab = b.pos();
    b.buf.extend_from_slice(&1i32.to_le_bytes()); // n_ctors
    b.buf.extend_from_slice(&0i32.to_le_bytes()); // single_match
    let entries_at = b.pos();
    b.buf.extend_from_slice(&[0u8; 16]);
    b.write_i32(entries_at, 1); // tag (Some)
    b.write_i32(entries_at + 4, 1); // n_fields
    b.set_self_rel(entries_at + 8, some_name);
    b.set_self_rel(entries_at + 12, some_fields);
    b.set_self_rel(root + OFF_NAME, type_name);
    b.set_self_rel(root + OFF_CTORS, ctab);

    let v = cranelisp_intrinsics::vec_runtime::vec_new(2);
    let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 1);
    let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 2);
    let some_val = alloc_adt_for_test(1, &[v]);
    assert_eq!(fmt(some_val, &b, root), "(Option.Some [1 2])");
}

#[test]
fn bake_recursion_depth_guard_terminates() {
    // A blob deeper than MAX_DESCRIPTOR_DEPTH degrades to TypeVar — verify
    // the TypeVar kind renders as a bare value (the degrade target). This is
    // the terminating behaviour for recursive/cyclic ADTs.
    let mut b = DescriptorBlob::new();
    let d = b.reserve_desc();
    b.set_kind(d, DescriptorKind::TypeVar);
    assert_eq!(fmt(123, &b, d), "123");
}

// Allocate a heap ADT cell `[hdr | tag | field0..]` using the runtime
// allocator, matching the base-pointer convention the walker reads.
fn alloc_adt_for_test(tag: i64, fields: &[i64]) -> i64 {
    let payload = (1 + fields.len()) * 8;
    let base = cranelisp_intrinsics::alloc_with_rc(payload) as i64;
    unsafe {
        *((base as *mut u8).add(16) as *mut i64) = tag;
        for (i, &f) in fields.iter().enumerate() {
            *((base as *mut u8).add(24 + i * 8) as *mut i64) = f;
        }
    }
    base
}

// ── Discovery-set tests (S76 §5) ──────────────────────────────────────────

fn fn_scheme(params: Vec<Type>, ret: Type) -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Fn(params, Box::new(ret)),
    }
}

/// Insert a Def with a GOT slot + a fake non-zero code pointer.
fn insert_fn(table: &mut SymbolTable<(), ()>, name: &str, scheme: Scheme, fake_ptr: Option<usize>) {
    let symbol = Symbol::from(name);
    let slot = table
        .install_concrete(
            symbol.clone(),
            scheme,
            vec![],
            None,
            0,
            CallableOrigin::Plain,
            Realization::Body {
                view: MonoDefnVariant {
                    name: symbol.clone(),
                    params: vec![],
                    body: MonoExpr::IntLit {
                        value: 0,
                        span: Span::SYNTHETIC,
                        ty: ConcreteType::Int,
                    },
                    span: Span::SYNTHETIC,
                    mode_summary: None,
                },
                code: None,
            },
            None,
            vec![],
            Visibility::Public,
        )
        .expect("install trace-discovery fixture")
        .index();
    if let Some(fake_ptr) = fake_ptr {
        table.got.store_slot(slot, fake_ptr as *const u8);
    }
}

#[test]
fn discovery_includes_all_modules_and_primitives() {
    let tables: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();

    let mut user = SymbolTable::<(), ()>::new(ModuleFullPath::from("user"));
    insert_fn(
        &mut user,
        "fact",
        fn_scheme(vec![Type::Int], Type::Int),
        Some(0x1000),
    );
    tables.insert(ModuleFullPath::from("user"), user);

    // The synthetic `primitives` module: entries carry code: None but the
    // GOT slot holds the fn ptr. Discovery must pick it up (no project-root
    // filter, primitives included).
    let mut prims = SymbolTable::<(), ()>::new(ModuleFullPath::from("primitives"));
    let primitive_slot = prims
        .install_extern(
            Symbol::from("str-concat"),
            fn_scheme(vec![Type::String, Type::String], Type::String),
            vec![],
            None,
            0,
            None,
            None,
            Visibility::Public,
        )
        .expect("install primitive discovery fixture")
        .index();
    prims.got.store_slot(primitive_slot, 0x2000 as *const u8);
    tables.insert(ModuleFullPath::from("primitives"), prims);

    let traced = discover_traced_fns_from_tables(&tables);
    let names: Vec<&str> = traced.iter().map(|t| t.name.as_str()).collect();
    assert!(
        names.contains(&"user/fact"),
        "user fn must be discovered: {names:?}"
    );
    assert!(
        names.contains(&"primitives/str-concat"),
        "primitive must be discovered (all symbol tables, primitives included): {names:?}"
    );
    // Arity + types come from the scheme.
    let prim = traced
        .iter()
        .find(|t| t.name == "primitives/str-concat")
        .unwrap();
    assert_eq!(prim.arity, 2);
    assert_eq!(prim.param_types, vec![Type::String, Type::String]);
    assert_eq!(prim.result_type, Type::String);
    assert_eq!(prim.module_path, ModuleFullPath::from("primitives"));
    assert_eq!(prim.got_slot, prims_slot_of_str_concat(&tables));
}

/// Read back the GOT slot the discovery should have recorded for the
/// primitive `str-concat` (the discovery records `got_slot`, not the raw
/// code pointer, since the wrapper reaches the original via a runtime
/// GOT-slot load — FIXME 0275).
fn prims_slot_of_str_concat(tables: &DashMap<ModuleFullPath, SymbolTable<(), ()>>) -> usize {
    let g = tables.get(&ModuleFullPath::from("primitives")).unwrap();
    match g.get("str-concat") {
        Some(entry) => entry
            .callable_got_slot()
            .expect("str-concat must be a got-slotted Def"),
        _ => panic!("str-concat must be a got-slotted Def"),
    }
}

#[test]
fn discovery_skips_constrained_poly_base_and_overloaded() {
    let tables: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();
    let mut m = SymbolTable::<(), ()>::new(ModuleFullPath::from("user"));

    // Constrained-poly base name (dispatch placeholder) — skipped.
    m.install_template(
        Symbol::from("add"),
        fn_scheme(vec![Type::Var(0), Type::Var(0)], Type::Var(0)),
        vec![],
        None,
        0,
        CallableOrigin::Plain,
        TemplateBody::Ast(template_variant()),
        TemplateKind::Constrained(Box::new(cranelisp_types::ConstrainedMeta::new(
            HashMap::new(),
        ))),
        vec![],
        Visibility::Public,
    )
    .expect("install constrained template fixture");
    // A template overload arm is a dispatch source, not a codegen body.
    m.install_overloaded(
        Symbol::from("show"),
        None,
        0,
        vec![CallableArmDraft::template(
            Scheme {
                type_vars: vec![0],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
            },
            vec![Symbol::from("x")],
            TemplateBody::Ast(template_variant()),
            TemplateKind::Parametric,
            vec![],
        )],
        Visibility::Public,
    )
    .expect("install overload fixture");
    // A real mono fn — kept.
    insert_fn(
        &mut m,
        "double",
        fn_scheme(vec![Type::Int], Type::Int),
        Some(0x3200),
    );
    tables.insert(ModuleFullPath::from("user"), m);

    let traced = discover_traced_fns_from_tables(&tables);
    let names: Vec<&str> = traced.iter().map(|t| t.name.as_str()).collect();
    assert!(names.contains(&"user/double"), "mono fn kept: {names:?}");
    assert!(
        !names.contains(&"user/add"),
        "constrained-poly base skipped: {names:?}"
    );
    assert!(
        !names.contains(&"user/show"),
        "overloaded base skipped: {names:?}"
    );
}

#[test]
fn discovery_skips_empty_got_slots_and_non_fn_schemes() {
    let tables: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();
    let mut m = SymbolTable::<(), ()>::new(ModuleFullPath::from("user"));

    // Def with a got_slot but the GOT slot is 0 (unpopulated) — skipped.
    insert_fn(
        &mut m,
        "uncompiled",
        fn_scheme(vec![Type::Int], Type::Int),
        None,
    );
    // (no got.store_slot — slot stays null)

    // Non-Fn scheme (e.g. a zero-arg value) with a populated slot — skipped
    // (arity/types require Type::Fn).
    insert_fn(
        &mut m,
        "konst",
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
        Some(0x4000),
    );
    tables.insert(ModuleFullPath::from("user"), m);

    let traced = discover_traced_fns_from_tables(&tables);
    let names: Vec<&str> = traced.iter().map(|t| t.name.as_str()).collect();
    assert!(
        !names.contains(&"user/uncompiled"),
        "empty GOT slot skipped: {names:?}"
    );
    assert!(
        !names.contains(&"user/konst"),
        "non-Fn scheme skipped: {names:?}"
    );
}

// A minimal ConstrainedFn for the skip test. We only need the variant
// discriminator (`constrained_fn: Some(_)`), so any well-formed value works.
fn template_variant() -> DefnVariant {
    DefnVariant {
        params: vec![],
        body: Expr::IntLit {
            value: 0,
            span: Span::SYNTHETIC,
            inferred_type: None,
        },
        span: Span::SYNTHETIC,
    }
}

// ── Descriptor-bake memoization guard (FIXME 0340 timing fix) ─────────────
//
// The dominant `(trace …)` codegen cost was the EXPONENTIAL re-bake of a
// recursive / DAG-shaped ADT descriptor: `bake_descriptor` re-walked the
// whole type at every level up to `MAX_DESCRIPTOR_DEPTH`, so a recursive
// type (the `IntList = Nil | (Cons Int IntList)` shape below, exactly the
// recursion class of the `Sexp`/`SList` types every macro-clause wrapper
// carries) produced a blob whose size grew exponentially in depth — ~1.3s
// per wrapper × ~170 discovered fns ≈ 30s+ per trace form. The `BakeMemo`
// (cycle-break + DAG-share) collapses it to LINEAR in distinct types.
//
// This is a count-based guard at the bake seam: the recursive type is baked
// ONCE (its self-reference degrades to one `TypeVar` back-edge), so the blob
// stays small and bounded. Pre-fix the same input produced a blob orders of
// magnitude larger (and the bake did not terminate in reasonable time).

/// Build a recursive ADT `IntList = Nil | (Cons :Int :IntList)` into a
/// `<(), ()>` symbol table so `lookup_type_def` / `constructor_metas` can
/// resolve it. Returns the tables + the `IntList` ADT `Type`.
fn recursive_intlist_tables() -> (DashMap<ModuleFullPath, SymbolTable<(), ()>>, Type) {
    use cranelisp_types::{FQTypeName, TypeDefInfo, TypeName};

    let module = ModuleFullPath::from("user");
    let intlist_fqtn = FQTypeName {
        module: module.clone(),
        name: TypeName::from("IntList"),
    };
    let intlist_ty = Type::ADT(intlist_fqtn.clone(), vec![]);

    let mut st = SymbolTable::<(), ()>::new(module.clone());

    // The TypeDef entry (sum type: type name distinct from both ctors).
    crate::test_support::install_type_fixture(
        &mut st,
        Symbol::from("IntList"),
        TypeDefInfo {
            name: intlist_fqtn.clone(),
            type_params: vec![],
            constructors: vec![Symbol::from("Nil"), Symbol::from("Cons")],
        },
    );

    // Nil — nullary ctor (tag 0, no fields).
    crate::test_support::install_ctor_fixture(
        &mut st,
        Symbol::from("Nil"),
        fn_scheme(vec![], intlist_ty.clone()),
        vec![],
        intlist_fqtn.clone(),
        0,
        0,
        None,
        None,
        None,
    );

    // Cons — data ctor (tag 1): fields [Int, IntList] — the SECOND field is
    // the recursive self-reference that drove the exponential blow-up.
    crate::test_support::install_ctor_fixture(
        &mut st,
        Symbol::from("Cons"),
        fn_scheme(vec![Type::Int, intlist_ty.clone()], intlist_ty.clone()),
        vec![Symbol::from("head"), Symbol::from("tail")],
        intlist_fqtn,
        1,
        2,
        None,
        None,
        None,
    );

    let tables = DashMap::new();
    tables.insert(module, st);
    (tables, intlist_ty)
}

// spec: design/arch/dotted-ctor-canonical-keys.md §10.3 (BU-1, loud-miss) —
// pattern position resolves a ctor by its STORAGE `FQSymbol` through
// `CompileContext::ctor_meta_at`: a DIRECT keyed read (deterministic, no name
// resolution, no global fallback). A key that resolves to a real ctor `Def`
// yields its `(FQTypeName, CtorMeta)`; a key that resolves to NO `Def` yields
// `None` — the precondition on which `compile_constructor_pattern` raises the
// hard `CodegenError` ("keying drift") instead of silently mis-tagging (P18).
#[test]
fn ctor_meta_at_keyed_read_hits_real_def_and_misses_are_loud() {
    let (tables, _ty) = recursive_intlist_tables();
    let module = ModuleFullPath::from("user");
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).unwrap();
    let iid = crate::jit::declare_intrinsics_generic(jit.jit_module()).unwrap();
    let func_ids: std::collections::HashMap<Symbol, cranelift_module::FuncId> =
        std::collections::HashMap::new();
    let func_arities: std::collections::HashMap<Symbol, usize> = std::collections::HashMap::new();
    let ctx = crate::compiler::CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: &tables,
        current_module: module.clone(),
        alloc_func_id: iid.alloc,
        dealloc_func_id: iid.dealloc.unwrap(),
        alloc_string_func_id: iid.alloc_string,
        panic: iid.panic,
        vec_new_func_id: iid.vec_new,
        vec_drop_func_id: iid.vec_drop,
    };

    // HIT: the storage key of the data ctor resolves to its `Def` — 2 fields,
    // tag 1, owned by `IntList`. The deterministic answer, no iteration order.
    let cons_fq = cranelisp_types::FQSymbol {
        module: module.clone(),
        symbol: Symbol::from("Cons"),
    };
    let (fqtn, meta) = ctx
        .ctor_meta_at(&cons_fq)
        .expect("Cons is fully declared")
        .expect("Cons storage key hits its Def");
    assert_eq!(fqtn.name.as_ref(), "IntList");
    assert_eq!(meta.tag, 1);
    assert_eq!(meta.fields.len(), 2);

    // MISS (loud-miss precondition): a key that no `Def` lives under yields
    // `None`. In `compile_constructor_pattern` a `Some(resolved_ctor)` landing
    // here is keying drift → hard `CodegenError`, never a silent mis-tag.
    let ghost = cranelisp_types::FQSymbol {
        module,
        symbol: Symbol::from("IntList.Ghost"),
    };
    assert!(
        matches!(ctx.ctor_meta_at(&ghost), Ok(None)),
        "a storage key with no Def is a None (the §10.3 hard-error precondition)"
    );
}

/// Run `body` against a real (throwaway) `FnCompiler` over a JIT module whose
/// context reads `tables` as module `user`.
fn with_bake_compiler<R>(
    tables: &DashMap<ModuleFullPath, SymbolTable<(), ()>>,
    body: impl FnOnce(&mut crate::compiler::FnCompiler<'_, cranelift_jit::JITModule, (), ()>) -> R,
) -> R {
    use cranelift::codegen::ir::{Function, UserFuncName};
    use cranelift::prelude::*;

    let mut jit = crate::jit::Jit::new_with_symbols(&[]).unwrap();
    let intrinsic_ids = crate::jit::declare_intrinsics_generic(jit.jit_module()).unwrap();
    let func_ids: std::collections::HashMap<Symbol, cranelift_module::FuncId> =
        std::collections::HashMap::new();
    let func_arities: std::collections::HashMap<Symbol, usize> = std::collections::HashMap::new();

    let ctx = crate::compiler::CompileContext {
        func_ids: &func_ids,
        func_arities: &func_arities,
        symbol_tables: tables,
        current_module: ModuleFullPath::from("user"),
        alloc_func_id: intrinsic_ids.alloc,
        dealloc_func_id: intrinsic_ids.dealloc.unwrap(),
        alloc_string_func_id: intrinsic_ids.alloc_string,
        panic: intrinsic_ids.panic,
        vec_new_func_id: intrinsic_ids.vec_new,
        vec_drop_func_id: intrinsic_ids.vec_drop,
    };

    let mut sig = jit.jit_module().make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig);
    let mut fctx = FunctionBuilderContext::new();
    let builder = FunctionBuilder::new(&mut func, &mut fctx);

    let mut glue = crate::test_support::probe_glue_registry(
        cranelisp_types::ModuleFullPath::from("user"),
        &intrinsic_ids,
    );
    let mut compiler = crate::compiler::FnCompiler::inner(
        builder,
        jit.jit_module(),
        ctx,
        crate::compiler::census::Frame::for_test(),
        &mut glue,
        1,
        crate::compiler::ownership_plan::OwnershipPlan::default(),
    );
    body(&mut compiler)
}

/// Drive `bake_descriptor_blob` for a `TracedFnInfo` whose param/result is
/// the recursive `IntList` ADT, returning the emitted blob's byte length and
/// descriptor record count.
fn bake_recursive_intlist_blob_size() -> (usize, usize) {
    let (tables, intlist_ty) = recursive_intlist_tables();
    let module_path = ModuleFullPath::from("user");
    with_bake_compiler(&tables, |compiler| {
        let tf = TracedFnInfo {
            name: "user/sum".to_string(),
            module_path,
            got_slot: 0,
            arity: 1,
            param_types: vec![intlist_ty.clone()],
            result_type: intlist_ty,
        };

        // Bake via the production path; then re-bake the same type set into a
        // standalone blob to count records (the production blob is consumed by
        // define_data, so re-run bake_descriptor for the count).
        let _set = compiler
            .bake_descriptor_blob(&tf, cranelisp_types::Span::SYNTHETIC)
            .expect("bake_descriptor_blob");

        // Re-bake into a standalone DescriptorBlob to measure size + record count.
        let mut blob = DescriptorBlob::new();
        let mut memo = BakeMemo::new();
        let p = compiler
            .bake_descriptor(
                &mut blob,
                &mut memo,
                &tf.param_types[0],
                0,
                cranelisp_types::Span::SYNTHETIC,
            )
            .expect("bake param");
        let _r = compiler
            .bake_descriptor(
                &mut blob,
                &mut memo,
                &tf.result_type,
                0,
                cranelisp_types::Span::SYNTHETIC,
            )
            .expect("bake result");
        // `done` records one entry per distinct ADT baked (Int/Bool/etc are not
        // memoized — only compound ADT/Vec types are). For IntList the distinct
        // ADT set is {IntList} ⇒ exactly one done-entry, and the param + result
        // (both IntList) SHARE it (DAG).
        assert_eq!(
            memo.done.len(),
            1,
            "exactly one distinct ADT baked (IntList)"
        );
        assert_eq!(
            p, _r,
            "param and result are the same type ⇒ DAG-shared (same blob offset)"
        );
        (blob.buf.len(), memo.done.len())
    })
}

// spec: design/backend/trace-codegen.md §3 — the baker turns a type whose
//       arguments do not pair with its constructors' declared parameters into
//       a keying error located at the trace form, not a mis-typed descriptor.
#[test]
fn bake_refuses_an_instantiation_whose_arguments_do_not_pair() {
    let (tables, _) = recursive_intlist_tables();
    let fqtn = cranelisp_types::FQTypeName {
        module: ModuleFullPath::from("user"),
        name: cranelisp_types::TypeName::from("IntList"),
    };
    // `IntList` declares no parameter; one argument is an arity mismatch.
    let mis_instantiated = Type::ADT(fqtn, vec![Type::Int]);
    let span = cranelisp_types::Span::new(7, 19);
    let err = with_bake_compiler(&tables, |compiler| {
        let mut blob = DescriptorBlob::new();
        let mut memo = BakeMemo::new();
        compiler
            .bake_descriptor(&mut blob, &mut memo, &mis_instantiated, 0, span)
            .expect_err("an unpairable instantiation is refused")
    });
    let CranelispError::CodegenError { message, location } = err else {
        panic!("expected a codegen error, got {err:?}");
    };
    assert!(
        message.contains("keying drift") && message.contains("user/IntList.Nil"),
        "names the constructor and the keying class: {message}"
    );
    assert_eq!(
        format!("{location:?}"),
        format!("{:?}", ErrorLocation::from_span(span)),
        "located at the trace form"
    );
}

#[test]
fn recursive_adt_descriptor_bake_is_bounded_not_exponential() {
    // The recursive IntList descriptor blob must be SMALL — the recursion
    // terminates at the self-reference back-edge (one TypeVar), not after 16
    // exponential levels. A pre-fix bake produced a blob of many KB (and ran
    // for ~1s); the memoized bake is a few hundred bytes.
    let (blob_len, distinct) = bake_recursive_intlist_blob_size();
    assert_eq!(distinct, 1, "IntList baked once (linear in distinct types)");
    assert!(
        blob_len < 1024,
        "recursive-ADT descriptor blob must stay bounded (memoized cycle-break); \
         got {blob_len} bytes — a non-memoized exponential re-bake would be far larger"
    );
}

// spec: design/backend/trace-codegen.md §2 rule 1 (M-1038, backend row) — a
// spark site inside a trace form emits the ordinary create-gate: the call to
// `cranelisp_spark_budget_try_reserve`, which declines at run time while the
// thread records. The trace takes its GOT-swap path (one published callable).
#[test]
fn trace_form_spark_site_emits_the_create_gate() {
    use cranelisp_types::{Defn, Expr};
    let probe = Symbol::from("trace_spark_probe");
    let call = |at: u32| Expr::Apply {
        callee: Box::new(Expr::Var {
            name: probe.clone(),
            span: Span::new(at, at + 1),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        }),
        args: vec![],
        span: Span::new(at, at + 1),
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let body = Expr::Trace {
        modules: vec![],
        body: Box::new(Expr::Let {
            bindings: vec![(Symbol::from("a"), call(1)), (Symbol::from("b"), call(3))],
            body: Box::new(Expr::IntLit {
                value: 0,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::Int)),
            }),
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(Type::Int)),
        }),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let defn = Defn {
        name: probe.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let user = ModuleFullPath::from("user");
    let mut table = SymbolTable::new(user.clone());
    crate::test_support::insert_user_fn_stub(&mut table, "trace_spark_probe", 0);
    insert_fn(
        &mut table,
        "published",
        fn_scheme(vec![Type::Int], Type::Int),
        Some(0x4100),
    );
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    tables.insert(user.clone(), table);
    let targets = crate::test_support::call_carriers(defn.body(), &user, &["trace_spark_probe"]);
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).expect("JIT construction");
    let clif =
        crate::test_support::probe_defn_clif(&defn, &[], &targets, &tables, user, jit.jit_module());
    let reserve = match jit
        .jit_module()
        .get_name("cranelisp_spark_budget_try_reserve")
    {
        Some(cranelift_module::FuncOrDataId::Func(id)) => id,
        other => panic!("the create-gate's reserve is not declared ({other:?})\n{clif}"),
    };
    let reserve_ref = crate::test_support::clif_func_ref(&clif, reserve);
    assert!(
        clif.contains(&format!("call {reserve_ref}(")),
        "the trace body's spark site calls the create-gate\n{clif}"
    );
    let swap = match jit.jit_module().get_name("cranelisp_trace_swap_got") {
        Some(cranelift_module::FuncOrDataId::Func(id)) => id,
        other => panic!("the trace's GOT swap is not declared ({other:?})\n{clif}"),
    };
    let swap_ref = crate::test_support::clif_func_ref(&clif, swap);
    assert!(
        clif.contains(&format!("call {swap_ref}(")),
        "the trace takes its swap path\n{clif}"
    );
}
