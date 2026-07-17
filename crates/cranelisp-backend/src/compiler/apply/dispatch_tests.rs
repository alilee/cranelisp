//! Relocated crate-root dispatch tests (FIXME 0495 step 1): trait-method primitive dispatch + platform-effect fn-name stamping through the apply/resolution path. Verbatim relocation from `src/tests.rs`.

use crate::test_support::*;


// --- Ring 2A: TraitMethod dispatch tests ---

// spec: 07-traits §7.7, appendix-a-builtins §A.3 — Num.+ primitive dispatch inlines to add-i64.
//
// Per Decision 43 + FIXME 0185: backend has no trait knowledge. The
// pre-D43 shape (TraitMethod with `(Num, "+", Int)` → backend-side
// `primitive_for_trait_method` lookup → inline IR) is deleted. The
// post-D43 path is: typecheck emits `ResolvedCall::BuiltinFn { name:
// "add-i64" }` directly for primitive-implemented operators; backend's
// inline-substitution path matches by Symbol only. The test asserts
// this end-to-end: `BuiltinFn { name: "add-i64" }` → inline iadd → 7.
#[test]
fn test_trait_method_dispatch_inline_add() {
    // (+ 3 4) post-D43 = BuiltinFn add-i64 (typecheck resolves the
    // primitive directly, not a TraitMethod).
    let apply_span = Span::new(100, 110);
    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("+"),
            span: Span::new(101, 102),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::IntLit { value: 3, span: Span::new(103, 104), inferred_type: None },
            Expr::IntLit { value: 4, span: Span::new(105, 106), inferred_type: None },
        ],
        span: apply_span,
        resolved_call: None,
        inferred_type: None,
    };

    let mut check = empty_check();
    check.method_resolutions.insert(
        apply_span,
        cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("add-i64"),
        },
    );

    let value = test_compile_and_run(&expr, &check, &empty_tables())
        .expect("BuiltinFn add-i64 should compile inline");
    assert_eq!(value, 7);
}


// spec: 07-traits §7.7, appendix-a-builtins §A.3 — Eq.= primitive dispatch on Bool.
//
// Per Decision 43 + FIXME 0185: same shape change as the Num.+ test.
// Post-D43 typecheck emits `BuiltinFn { name: "eq-bool" }` for the
// primitive-implemented `=` on Bool. Backend's inline path matches by
// Symbol; the result is the `icmp eq` IR returning 1 (true).
#[test]
fn test_trait_method_dispatch_eq_bool() {
    // (= true true) post-D43 = BuiltinFn eq-bool.
    let apply_span = Span::new(200, 210);
    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("="),
            span: Span::new(201, 202),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::BoolLit { value: true, span: Span::new(203, 207), inferred_type: None },
            Expr::BoolLit { value: true, span: Span::new(208, 212), inferred_type: None },
        ],
        span: apply_span,
        resolved_call: None,
        inferred_type: None,
    };

    let mut check = empty_check();
    check.method_resolutions.insert(
        apply_span,
        cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("eq-bool"),
        },
    );

    let value = test_compile_and_run(&expr, &check, &empty_tables())
        .expect("BuiltinFn eq-bool should compile inline");
    assert_eq!(value, 1); // true == true → true (1)
}


// spec: design/arch/bounded-contexts.md §5 invariant 9 (S81 / FIXME 0327,
//       the fault-guarded dispatch funnel step 2/4 — fault-path fn-name).
//
// The residual FIXME-0337 gap: a BARE imported platform-effect call
// `(crash)` carries `resolved_call: None`, so it reaches dispatch via the
// plain `compile_var_apply` → `compile_direct_call` path, NOT the
// `ResolvedCall::BuiltinFn` arm. The original step-2 stamp lived ONLY in the
// `BuiltinFn` arm, so the var-apply path emitted the GOT-indirect call with
// NO field-3 stamp — the fn-name handle stayed null and the surfaced
// DispatchError degraded to `<unknown>` (on BOTH the happy and fault paths).
//
// The fix sites the stamp at the single GOT-indirect dispatch chokepoint
// (`compile_direct_call`), so EVERY dispatch path stamps. This test pins
// that: a hand-built `caller` defn whose body is `(Apply (Var "crash") []
// resolved_call=None)` — the exact bare-import shape the bug exposed — must
// compile to CLIF that STORES the baked name into the returned Effect node's
// field-3 (absolute offset `HeapHeader::SIZE + IO_EFFECT_FN_NAME_OFFSET` = 40),
// AFTER the dispatch `call_indirect` and BEFORE `return` (node-construction
// time, before the force — so the name survives a thunk panic on the fault
// path). A non-platform-effect callee must NOT emit such a store.
#[test]
fn platform_effect_dispatch_stamps_fn_name_on_bare_import_var_apply_path() {
    use cranelisp_types::{DefKind, FQSymbol, HeapHeader, ModuleEntry, Scheme};

    // The absolute byte offset of the Effect node's fn-name field (field-3),
    // composed from the public ABI constants — must equal 40 today and match
    // the (module-private) EFFECT_FN_NAME_ABS_OFFSET the stamp emits.
    let field3_off: i64 =
        HeapHeader::SIZE as i64 + cranelisp_platform::IO_EFFECT_FN_NAME_OFFSET;

    let plat = ModuleFullPath::from("platform.boom");
    let user = ModuleFullPath::from("user");

    // `caller` body: `(crash)` with resolved_call: None — the bare-import
    // var-apply shape, NOT a `ResolvedCall::BuiltinFn`.
    let caller = Defn {
        name: Symbol::from("caller"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("crash"),
                    span: Span::SYNTHETIC,
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![],
                span: Span::SYNTHETIC,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    // platform.boom: `crash` is a got-slotted PlatformEffect (the only kind
    // that stamps). Slot 0 in the platform GOT.
    {
        let mut st = SymbolTable::new(plat.clone());
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        st.insert(
            Symbol::from("crash"),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::PlatformEffect {
                    scheduling_class: Default::default(),
                    poll_shape: false,
                    got_slot: 0,
                    mode_summary: None,
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: None,
                codegen_view: None,
                code: None,
                value_use: false,
            },
        );
        tables.insert(plat.clone(), st);
    }
    // user: imports `crash` from platform.boom + defines `caller` at slot 0.
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        st.insert(
            Symbol::from("crash"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: plat.clone(),
                    symbol: Symbol::from("crash"),
                },
                visibility: Visibility::Public,
            },
        );
        // W1 (KC-W0-6): `caller`'s `(crash)` reads the callee's `resolved_target`.
        // `crash` is an Import in `user`, so its TERMINAL storage key is the
        // effect's home `platform.boom/crash` (what `storage_fq()` records) — the
        // direct keyed read (`entry_at`) lands on the PlatformEffect Def there.
        let mut caller_targets: HashMap<Span, FQSymbol> = HashMap::new();
        caller_targets.insert(
            Span::SYNTHETIC,
            FQSymbol { module: plat.clone(), symbol: Symbol::from("crash") },
        );
        st.insert(
            Symbol::from("caller"),
            make_def_entry_slot_with_targets(caller.clone(), 0, &caller_targets),
        );
        tables.insert(user.clone(), st);
    }

    let mut obj = make_object_module();
    let artifacts = compile_to_module(
        user.clone(),
        std::slice::from_ref(&caller.name),
        &tables,
        &mut obj,
        true, // capture_clif
    )
    .expect("compile caller calling a bare-imported platform effect");

    // The emitted CLIF for `caller` must store into field-3 at +40. The store
    // is the fn-name stamp; its absence is the FIXME-0337 `<unknown>` bug.
    let store_at_field3 = format!("+{field3_off}");
    assert!(
        artifacts.clif_ir.contains("store") && artifacts.clif_ir.contains(&store_at_field3),
        "bare-import platform-effect dispatch (resolved_call: None) MUST stamp \
         the fn-name into the Effect node's field-3 (store at {store_at_field3}); \
         the var-apply path was missing the stamp (FIXME 0337). CLIF:\n{}",
        artifacts.clif_ir,
    );
}


// spec: design/arch/bounded-contexts.md §5 invariant 9 (negative) — a NON
//       platform-effect callee dispatched GOT-indirect must NOT stamp
//       field-3: its result is not an Effect node and writing +40 would
//       corrupt an unrelated allocation. `resolve_platform_effect_target`
//       returns None for a plain UserFn, so no store is emitted.
#[test]
fn non_platform_effect_dispatch_does_not_stamp_field3() {
    let user = ModuleFullPath::from("user");
    // A plain user fn `helper` (UserFn, slotted) and a `caller` that calls it
    // with resolved_call: None (the same var-apply path).
    let helper = make_int_defn("helper", 7);
    let caller = Defn {
        name: Symbol::from("caller"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("helper"),
                    span: Span::SYNTHETIC,
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![],
                span: Span::SYNTHETIC,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        // W1 (KC-W0-6): `caller`'s `(helper)` reads the callee's `resolved_target`
        // — the plain user fn's own home `user/helper`.
        let mut caller_targets: HashMap<Span, cranelisp_types::FQSymbol> = HashMap::new();
        caller_targets.insert(
            Span::SYNTHETIC,
            cranelisp_types::FQSymbol { module: user.clone(), symbol: Symbol::from("helper") },
        );
        st.insert(helper.name.clone(), make_def_entry_slot(helper.clone(), 0));
        st.insert(
            caller.name.clone(),
            make_def_entry_slot_with_targets(caller.clone(), 1, &caller_targets),
        );
        tables.insert(user.clone(), st);
    }

    let field3_off: i64 = cranelisp_types::HeapHeader::SIZE as i64
        + cranelisp_platform::IO_EFFECT_FN_NAME_OFFSET;
    let store_at_field3 = format!("+{field3_off}");

    let mut obj = make_object_module();
    let artifacts = compile_to_module(
        user.clone(),
        std::slice::from_ref(&caller.name),
        &tables,
        &mut obj,
        true,
    )
    .expect("compile caller calling a plain user fn");

    assert!(
        !artifacts.clif_ir.contains(&store_at_field3),
        "a non-platform-effect GOT-indirect dispatch MUST NOT stamp field-3 \
         (no store at {store_at_field3}); only DefKind::PlatformEffect stamps. CLIF:\n{}",
        artifacts.clif_ir,
    );
}
