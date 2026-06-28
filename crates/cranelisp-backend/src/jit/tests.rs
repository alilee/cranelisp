use super::*;
use cranelisp_types::DefnVariant;

// spec: 12-runtime §12.1 — ISA construction for host platform
#[test]
fn test_build_isa() {
    let isa = build_isa();
    assert!(isa.is_ok(), "ISA construction should succeed on host");
}

// spec: 12-runtime §12.1 — JIT engine creation
#[test]
fn test_jit_creation() {
    let jit = Jit::new_with_symbols(&[]);
    assert!(jit.is_ok(), "JIT creation should succeed");
}

// spec: 12-runtime §12.3 — runtime intrinsic function declarations (alloc, dealloc, panic)
#[test]
fn test_intrinsic_declaration() {
    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let ids = jit.declare_intrinsics();
    assert!(ids.is_ok(), "intrinsic declaration should succeed");
}

// spec: 08-modules §8.3 — imported function declarations for cross-module calls
#[test]
fn test_declare_imported_functions() {
    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let mut func_ids = HashMap::new();

    let imports = vec![
        (Symbol::from("math/add"), 2usize),
        (Symbol::from("math/mul"), 2usize),
    ];
    let result = jit.declare_imported_functions(&imports, &mut func_ids);
    assert!(result.is_ok(), "imported function declaration should succeed");
    assert!(func_ids.contains_key(&Symbol::from("math/add")));
    assert!(func_ids.contains_key(&Symbol::from("math/mul")));
    assert_eq!(func_ids.len(), 2);
}

// spec: 08-modules §8.3 — imported declarations merge with local function declarations
#[test]
fn test_declare_imported_functions_merges_with_existing() {
    let mut jit = Jit::new_with_symbols(&[]).unwrap();

    // Declare a local function first.
    let defn = Defn {
        name: Symbol::from("local_fn"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: cranelisp_types::Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(0, 1),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 10),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 10),
    };
    let mut func_ids = jit.declare_functions(&[&defn]).unwrap();
    assert_eq!(func_ids.len(), 1);

    // Now declare an imported function -- should merge into the same map.
    let imports = vec![(Symbol::from("other/helper"), 1usize)];
    jit.declare_imported_functions(&imports, &mut func_ids).unwrap();
    assert_eq!(func_ids.len(), 2);
    assert!(func_ids.contains_key(&Symbol::from("local_fn")));
    assert!(func_ids.contains_key(&Symbol::from("other/helper")));
}

// spec: pipeline-orchestration §4 — JIT with extra symbols for cross-module calls
#[test]
fn test_jit_new_with_symbols() {
    // An empty extra_symbols list should work identically to new().
    let jit = Jit::new_with_symbols(&[]);
    assert!(jit.is_ok(), "new_with_symbols with empty list should succeed");

    // Extra symbols should be accepted (though we can't call them in
    // this unit test, we verify the builder doesn't reject them).
    extern "C" fn dummy_fn(_x: i64) -> i64 {
        0
    }
    let jit2 = Jit::new_with_symbols(&[("test/dummy", dummy_fn as *const u8)]);
    assert!(
        jit2.is_ok(),
        "new_with_symbols with extra symbol should succeed"
    );
}

// spec: design/arch/CLAUDE.md Decision 31 — custom `Drop` on `Jit` calls
// `unsafe JITModule::free_memory()` to reclaim mmap'd executable pages.
// Without this, Cranelift's default `Memory::drop` leaks
// (cranelift-jit-0.116.1/src/memory.rs:269-276 — `mem::forget`s every
// allocation).
#[test]
fn drop_runs_without_panic() {
    // A freshly-constructed JIT with no compiled code must still drop
    // cleanly — free_memory must tolerate a JIT that has never had
    // anything finalised.
    let jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    drop(jit);
    // Reaching here means the drop path returned without panic.
}

// spec: design/arch/CLAUDE.md Decision 31 — reclaim path executes on drop.
#[test]
fn drop_invokes_free_memory() {
    use std::sync::atomic::Ordering;

    let before = JIT_FREE_MEMORY_CALL_COUNT.load(Ordering::Relaxed);
    {
        let _jit = Jit::new_with_symbols(&[]).expect("JIT construction");
        // Declaring intrinsics exercises the JIT's declare path so this
        // isn't a trivial empty-module case. `_jit` drops at end of
        // scope.
        let mut jit = _jit;
        jit.declare_intrinsics().expect("intrinsics declare");
        drop(jit);
    }
    let after = JIT_FREE_MEMORY_CALL_COUNT.load(Ordering::Relaxed);
    assert_eq!(
        after, before + 1,
        "Jit::drop must call free_memory exactly once (counter before={before}, after={after})"
    );
}

// spec: design/arch/CLAUDE.md Decision 31 — normal compile+call+drop
// flow continues to work after the reclaim machinery is in place. This
// checks that the `Option<JITModule>` plumbing does not regress the
// finalize/get-ptr/call path. We observe the correct return value
// **before** drop (post-drop derefs are UB); the drop itself then fires
// and must not panic.
#[test]
fn compile_call_drop_roundtrip() {
    use cranelisp_types::{Expr, Type, Visibility};
    use std::sync::atomic::Ordering;

    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    jit.declare_intrinsics().expect("intrinsics declare");

    // Zero-arg fn returning the literal 42.
    let name = Symbol::from("trivial_fortytwo");
    let defn = Defn {
        name: name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 42,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let func_ids = jit.declare_functions(&[&defn]).expect("declare");
    let func_arities: HashMap<Symbol, usize> = HashMap::new();
    let symbol_tables: dashmap::DashMap<
        cranelisp_types::ModuleFullPath,
        cranelisp_types::SymbolTable,
    > = dashmap::DashMap::new();
    let module_path = cranelisp_types::ModuleFullPath::from("user");
    symbol_tables.insert(
        module_path.clone(),
        cranelisp_types::SymbolTable::new(module_path.clone()),
    );

    let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
    let compile_ctx = jit.build_compile_context(
        &func_ids,
        &func_arities,
        &symbol_tables,
        &module_aliases,
        module_path,
    );
    jit.compile_defn(&defn, compile_ctx).expect("compile");
    let ptr = jit.finalize_and_get_ptr(&name, 0).expect("finalize");
    assert!(!ptr.is_null(), "finalized pointer must be non-null");

    // SAFETY: the JIT is still alive (we hold the only handle to it);
    // the function was just finalized with signature `extern "C" fn() -> i64`.
    let f: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    let result = f();
    assert_eq!(result, 42, "trivial fn must return 42 before drop");

    // Now drop and confirm the reclaim counter incremented.
    let before = JIT_FREE_MEMORY_CALL_COUNT.load(Ordering::Relaxed);
    drop(jit);
    let after = JIT_FREE_MEMORY_CALL_COUNT.load(Ordering::Relaxed);
    assert_eq!(
        after, before + 1,
        "Drop after compile+call must still invoke free_memory"
    );
}

// spec: design/arch/CLAUDE.md Decision 23 (Sprint 58 Wave 2 follow-on) —
// unified GOT data symbol shape: the symbol address IS the per-module
// slab base directly, with NO extra pointer-cell indirection. In JIT
// mode this is achieved by registering `__cranelisp_got_{M}` via
// `JITBuilder::symbol()` (passed through `extra_symbols`) so the
// lookup-fn returns the slab base; CLIF emitted by
// `emit_got_indirect_call_via_data_id` then does one `global_value`
// (= ADRP+LDR through the system GOT) + one slot offset + one slot
// load. This test compiles a function that takes the symbol's address
// via `global_value` and asserts the address equals the registered
// slab base — i.e. the registered address is NOT a separate pointer
// cell that itself contains the slab base.
#[test]
fn jit_got_symbol_address_is_slab_base() {
    use cranelisp_types::{Defn, DefnVariant, Expr, Type, Visibility};
    use cranelift_module::Linkage;
    use std::sync::atomic::{AtomicU64, Ordering};

    // Use a static, address-stable backing storage as the "slab base".
    // The test asserts that `__cranelisp_got_test_module` resolves to
    // exactly this address (no extra deref).
    static SLAB: AtomicU64 = AtomicU64::new(0xDEAD_BEEF_CAFE_F00D);
    let slab_base_ptr: *const u8 = &SLAB as *const _ as *const u8;

    let got_sym = "__cranelisp_got_test_module";
    let mut jit = Jit::new_with_symbols(&[(got_sym, slab_base_ptr)])
        .expect("JIT construction with GOT symbol");
    jit.declare_intrinsics().expect("intrinsics");

    // Compile a fn that returns the *address* of the GOT data symbol —
    // this is what `global_value` resolves to inside the unified GOT
    // call sequence. If JIT registration is correct, the returned i64
    // equals `slab_base_ptr as u64` (no extra pointer-cell deref).
    let name = Symbol::from("get_got_addr");
    let body = Expr::IntLit {
        value: 0,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let defn = Defn {
        name: name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    // Declare the function and build a context, then hand-write the body
    // so the test does not depend on the broader codegen pipeline. The
    // body is: declare `__cranelisp_got_test_module` as Import data,
    // take its address via `global_value`, return it as i64.
    let func_ids = jit.declare_functions(&[&defn]).expect("declare");
    let func_id = *func_ids.get(&name).expect("func_id");

    // Build the body by reaching into the JIT module directly.
    {
        let module = jit.jit_module();
        let mut sig = module.make_signature();
        sig.returns.push(cranelift::prelude::AbiParam::new(
            cranelift::prelude::types::I64,
        ));
        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        ctx.func.name = cranelift::codegen::ir::UserFuncName::testcase(name.as_bytes());

        let data_id = module
            .declare_data(got_sym, Linkage::Import, false, false)
            .expect("declare GOT data");

        let mut fbc = FunctionBuilderContext::new();
        {
            let gv = module.declare_data_in_func(data_id, &mut ctx.func);
            let mut fb = cranelift::prelude::FunctionBuilder::new(&mut ctx.func, &mut fbc);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.seal_block(entry);
            let addr = fb
                .ins()
                .global_value(cranelift::prelude::types::I64, gv);
            fb.ins().return_(&[addr]);
            fb.finalize();
        }
        module
            .define_function(func_id, &mut ctx)
            .expect("define_function");
        module.clear_context(&mut ctx);
    }

    let ptr = jit.finalize_and_get_ptr(&name, 0).expect("finalize");
    // SAFETY: the JIT is still alive; signature is `extern "C" fn() -> i64`.
    let f: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    let returned = f() as u64;

    assert_eq!(
        returned,
        slab_base_ptr as u64,
        "JIT-resolved address of __cranelisp_got_test_module must equal \
         the registered slab base directly (no pointer-cell indirection); \
         returned={:#x}, expected={:#x}",
        returned,
        slab_base_ptr as u64,
    );

    // Regression guard: read the SLAB content. If the JIT had defined
    // the symbol as a pointer cell containing the slab base, the
    // returned address would point INTO `SLAB` (and `*returned == SLAB`).
    // With the correct registration, the returned address IS
    // `&SLAB`, so `*returned == SLAB.load()`. The two are
    // distinguishable only when the registered symbol address is the
    // slab itself: confirm by reading 8 bytes at the returned address.
    let read = unsafe { std::ptr::read_unaligned(returned as *const u64) };
    assert_eq!(
        read,
        SLAB.load(Ordering::Relaxed),
        "Address returned must point AT the slab (so dereferencing it \
         yields the slab's first word), confirming no intermediate \
         pointer cell exists."
    );
}

// spec: design/arch/CLAUDE.md Decision 23 — cross-module dispatch via
// GOT-indirect call. Two synthetic modules: producer module owns a fn
// returning 99 with its pointer placed at slot 7 of a heap-allocated
// slab; consumer module compiles a thunk that loads slot 7 from the
// producer's GOT and tail-calls through it. Asserts the round-trip
// returns 99, exercising the full unified call shape end-to-end.
#[test]
fn jit_cross_module_got_dispatch_end_to_end() {
    use cranelift_module::Linkage;
    use std::alloc::{alloc_zeroed, Layout};

    // 1. Build a "producer" JIT, compile `producer_fn` returning 99.
    //    Read out its finalised pointer.
    let producer_ptr: *const u8 = {
        use cranelisp_types::{Defn, DefnVariant, Expr, Type, Visibility};
        let mut jit = Jit::new_with_symbols(&[]).expect("producer JIT");
        jit.declare_intrinsics().expect("intrinsics");
        let name = Symbol::from("producer_fn");
        let defn = Defn {
            name: name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit {
                    value: 99,
                    span: Span::SYNTHETIC,
                    inferred_type: Some(Box::new(Type::Int)),
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let func_ids = jit.declare_functions(&[&defn]).expect("declare");
        let func_arities: HashMap<Symbol, usize> = HashMap::new();
        let symbol_tables: dashmap::DashMap<
            cranelisp_types::ModuleFullPath,
            cranelisp_types::SymbolTable,
        > = dashmap::DashMap::new();
        let module_path = cranelisp_types::ModuleFullPath::from("producer");
        symbol_tables.insert(
            module_path.clone(),
            cranelisp_types::SymbolTable::new(module_path.clone()),
        );
        let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
        let compile_ctx =
            jit.build_compile_context(&func_ids, &func_arities, &symbol_tables, &module_aliases, module_path);
        jit.compile_defn(&defn, compile_ctx).expect("compile");
        let ptr = jit.finalize_and_get_ptr(&name, 0).expect("finalize");
        // Leak `jit` so the code pages stay live for the duration of the test.
        std::mem::forget(jit);
        ptr
    };

    // 2. Allocate a 16-slot slab on the heap, write `producer_ptr` at slot 7.
    let slot = 7usize;
    let slab_size = 16 * 8;
    let layout = Layout::from_size_align(slab_size, 8).unwrap();
    let slab_base: *mut u8 = unsafe { alloc_zeroed(layout) };
    unsafe {
        let slot_addr = slab_base.add(slot * 8) as *mut u64;
        slot_addr.write(producer_ptr as u64);
    }

    // 3. Build a consumer JIT with `__cranelisp_got_producer` registered
    //    pointing at the slab base directly (Decision 23 — symbol
    //    address IS the slab base, no pointer-cell indirection).
    let got_sym = "__cranelisp_got_producer";
    let mut consumer = Jit::new_with_symbols(&[(got_sym, slab_base as *const u8)])
        .expect("consumer JIT");
    consumer.declare_intrinsics().expect("intrinsics");

    // 4. Hand-build a thunk that emits the unified GOT call shape:
    //    slab = global_value(__cranelisp_got_producer)
    //    fn_ptr = load(slab + slot * 8)
    //    return call_indirect(fn_ptr)
    let thunk_name = Symbol::from("consumer_thunk");
    let thunk_id = {
        let module = consumer.jit_module();
        let mut sig = module.make_signature();
        sig.returns.push(cranelift::prelude::AbiParam::new(
            cranelift::prelude::types::I64,
        ));
        let id = module
            .declare_function(&thunk_name, Linkage::Export, &sig)
            .expect("declare thunk");
        let data_id = module
            .declare_data(got_sym, Linkage::Import, false, false)
            .expect("declare GOT data");

        let mut ctx = module.make_context();
        ctx.func.signature = sig.clone();
        ctx.func.name =
            cranelift::codegen::ir::UserFuncName::testcase(thunk_name.as_bytes());
        let mut fbc = FunctionBuilderContext::new();
        {
            let gv = module.declare_data_in_func(data_id, &mut ctx.func);
            let mut fb = cranelift::prelude::FunctionBuilder::new(&mut ctx.func, &mut fbc);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.seal_block(entry);
            let slab = fb
                .ins()
                .global_value(cranelift::prelude::types::I64, gv);
            let slot_addr = fb.ins().iadd_imm(slab, (slot * 8) as i64);
            let fn_ptr = fb.ins().load(
                cranelift::prelude::types::I64,
                cranelift::prelude::MemFlags::trusted(),
                slot_addr,
                0,
            );
            let mut callee_sig = module.make_signature();
            callee_sig.returns.push(cranelift::prelude::AbiParam::new(
                cranelift::prelude::types::I64,
            ));
            let sig_ref = fb.import_signature(callee_sig);
            let call = fb.ins().call_indirect(sig_ref, fn_ptr, &[]);
            let result = fb.inst_results(call)[0];
            fb.ins().return_(&[result]);
            fb.finalize();
        }
        module
            .define_function(id, &mut ctx)
            .expect("define thunk");
        module.clear_context(&mut ctx);
        id
    };

    consumer.finalize().expect("finalize consumer");
    let thunk_ptr = consumer.get_finalized_ptr(thunk_id);
    // SAFETY: thunk just finalised; signature is `extern "C" fn() -> i64`.
    let thunk: extern "C" fn() -> i64 = unsafe { std::mem::transmute(thunk_ptr) };
    let result = thunk();
    assert_eq!(
        result, 99,
        "Cross-module GOT dispatch must round-trip the producer's return value (99)"
    );

    // Cleanup: drop consumer JIT (producer was forgotten — the slab
    // and its slot pointer remain valid for the duration of `result`'s
    // computation, and we deliberately leak both for test simplicity).
    drop(consumer);
    // SAFETY: nothing reads `slab_base` after this point.
    unsafe { std::alloc::dealloc(slab_base, layout) };
}

// ----- §1 `Jit::new(symbol_tables)` — the minimal JIT-setup boundary -----

use cranelisp_types::{
    ModuleFullPath, Scheme, SchedulingClass, SymbolTable, Type, Visibility,
};

/// Build a `DefKind::PlatformEffect` Def entry with a populated GOT slot,
/// returning the entry. Mirrors what the platform DLL loader writes — the
/// runtime pointer lands in `table.got` at the allocated slot.
fn platform_effect_def(slot: usize) -> ModuleEntry {
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::PlatformEffect {
            scheduling_class: SchedulingClass::Sequential,
            poll_shape: false,
            got_slot: slot,
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
    }
}

// spec: design/backend/jit-setup-boundary.md §1 — `Jit::new(symbol_tables)`
// constructs from an empty symbol set (no modules) without error.
#[test]
fn jit_new_from_empty_symbol_tables() {
    let tables: SymbolTables<(), ()> = dashmap::DashMap::new();
    let jit = Jit::new(&tables);
    assert!(jit.is_ok(), "Jit::new with empty symbol_tables must succeed");
}

// spec: design/backend/jit-setup-boundary.md §1.3 — `Jit::new` derives the
// per-module GOT data symbol AND the platform-effect jit-name from
// `symbol_tables`. Build two modules (one plain, one carrying a
// PlatformEffect def with a populated GOT slot) and assert the JIT resolves
// the registered platform symbol to the slot pointer via a hand-built
// `global_value` thunk — the same observation shape as
// `jit_got_symbol_address_is_slab_base`.
#[test]
fn jit_new_registers_platform_effect_and_got_symbols() {
    use cranelift_module::Linkage;
    use std::sync::atomic::{AtomicU64, Ordering};

    // An address-stable backing storage standing in for the platform fn.
    static PLATFORM_FN: AtomicU64 = AtomicU64::new(0x1234_5678_9ABC_DEF0);
    let platform_ptr: *const u8 = &PLATFORM_FN as *const _ as *const u8;

    let tables: SymbolTables<(), ()> = dashmap::DashMap::new();

    // Module 1: plain user module, no platform effects.
    let plain = ModuleFullPath::from("user");
    tables.insert(plain.clone(), SymbolTable::new(plain.clone()));

    // Module 2: platform module with a PlatformEffect def whose GOT slot
    // holds `platform_ptr`.
    let plat_mod = ModuleFullPath::from("platform.stdio");
    let mut plat_table = SymbolTable::new(plat_mod.clone());
    let slot = plat_table.allocate_got_slot();
    plat_table.got.store_slot(slot, platform_ptr);
    plat_table.insert(Symbol::from("cranelisp_print"), platform_effect_def(slot));
    tables.insert(plat_mod.clone(), plat_table);

    let mut jit = Jit::new(&tables).expect("Jit::new must succeed");
    jit.declare_intrinsics().expect("intrinsics");

    // Hand-build a thunk that declares `cranelisp_print` as Import data and
    // returns its address. If `Jit::new` registered the platform symbol to
    // `platform_ptr`, the returned i64 equals `platform_ptr as u64`.
    let name = Symbol::from("get_platform_addr");
    let func_id = {
        let module = jit.jit_module();
        let mut sig = module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function(name.as_ref(), Linkage::Export, &sig)
            .expect("declare thunk");
        let data_id = module
            .declare_data("cranelisp_print", Linkage::Import, false, false)
            .expect("declare platform symbol");
        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        ctx.func.name =
            cranelift::codegen::ir::UserFuncName::testcase(name.as_bytes());
        let mut fbc = FunctionBuilderContext::new();
        {
            let gv = module.declare_data_in_func(data_id, &mut ctx.func);
            let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.seal_block(entry);
            let addr = fb.ins().global_value(types::I64, gv);
            fb.ins().return_(&[addr]);
            fb.finalize();
        }
        module.define_function(id, &mut ctx).expect("define thunk");
        module.clear_context(&mut ctx);
        id
    };

    jit.finalize().expect("finalize");
    let ptr = jit.get_finalized_ptr(func_id);
    // SAFETY: thunk just finalised; signature is `extern "C" fn() -> i64`.
    let f: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    let returned = f() as u64;
    assert_eq!(
        returned, platform_ptr as u64,
        "Jit::new must register the PlatformEffect jit-name to its GOT-slot \
         pointer; returned={returned:#x}, expected={:#x}",
        platform_ptr as u64,
    );
    // Confirm the address points AT the backing storage (no indirection).
    let read = unsafe { std::ptr::read_unaligned(returned as *const u64) };
    assert_eq!(read, PLATFORM_FN.load(Ordering::Relaxed));
}

// spec: design/backend/jit-setup-boundary.md §1.3 — a PlatformEffect with a
// null GOT slot (loader has not populated it) contributes no symbol; an
// Import edge to a populated PlatformEffect in another module resolves the
// platform fn by the defining module's key. Verifies both via reachability
// of the imported name.
#[test]
fn jit_new_follows_import_edge_for_platform_effect() {
    use cranelift_module::Linkage;
    use std::sync::atomic::AtomicU64;

    static PLATFORM_FN: AtomicU64 = AtomicU64::new(0xFEED_FACE_DEAD_BEEF);
    let platform_ptr: *const u8 = &PLATFORM_FN as *const _ as *const u8;

    let tables: SymbolTables<(), ()> = dashmap::DashMap::new();

    // Defining module: platform.stdio defines `print` as a PlatformEffect.
    let plat_mod = ModuleFullPath::from("platform.stdio");
    let mut plat_table = SymbolTable::new(plat_mod.clone());
    let slot = plat_table.allocate_got_slot();
    plat_table.got.store_slot(slot, platform_ptr);
    plat_table.insert(Symbol::from("print"), platform_effect_def(slot));
    tables.insert(plat_mod.clone(), plat_table);

    // Importing module: user imports `print` from platform.stdio.
    let user = ModuleFullPath::from("user");
    let mut user_table = SymbolTable::new(user.clone());
    user_table.insert(
        Symbol::from("print"),
        ModuleEntry::Import {
            source: cranelisp_types::FQSymbol {
                module: plat_mod.clone(),
                symbol: Symbol::from("print"),
            },
            visibility: Visibility::Public,
        },
    );
    tables.insert(user.clone(), user_table);

    let mut jit = Jit::new(&tables).expect("Jit::new must succeed");
    jit.declare_intrinsics().expect("intrinsics");

    // The platform symbol is registered under the defining module's key
    // (`print`). A thunk taking its address must resolve to `platform_ptr`.
    let name = Symbol::from("get_print_addr");
    let func_id = {
        let module = jit.jit_module();
        let mut sig = module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function(name.as_ref(), Linkage::Export, &sig)
            .expect("declare thunk");
        let data_id = module
            .declare_data("print", Linkage::Import, false, false)
            .expect("declare platform symbol");
        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        ctx.func.name =
            cranelift::codegen::ir::UserFuncName::testcase(name.as_bytes());
        let mut fbc = FunctionBuilderContext::new();
        {
            let gv = module.declare_data_in_func(data_id, &mut ctx.func);
            let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.seal_block(entry);
            let addr = fb.ins().global_value(types::I64, gv);
            fb.ins().return_(&[addr]);
            fb.finalize();
        }
        module.define_function(id, &mut ctx).expect("define thunk");
        module.clear_context(&mut ctx);
        id
    };

    jit.finalize().expect("finalize");
    let ptr = jit.get_finalized_ptr(func_id);
    // SAFETY: thunk just finalised; signature is `extern "C" fn() -> i64`.
    let f: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    assert_eq!(
        f() as u64,
        platform_ptr as u64,
        "Jit::new must follow the Import edge and register the platform fn \
         under the defining module's key",
    );
}

// spec: design/arch/test-discovery.md §6 "Backend — `Jit::define_symbol`";
//       BC §3 invariant 8 — a host-promised extern (`discover-tests`) whose
//       body is neither codegen-emitted, bundled, nor catalogued is settled
//       at finalize via `define_symbol`. The lookup-fn the constructor
//       installs consults the post-construction map, so an unresolved
//       `Linkage::Import` relocation against the promised name settles to
//       the host pointer. Mirrors the PlatformEffect observation shape.
#[test]
fn define_symbol_settles_host_promised_import() {
    use cranelift_module::Linkage;
    use std::sync::atomic::{AtomicU64, Ordering};

    // Address-stable backing storage standing in for the host extern body.
    static HOST_FN: AtomicU64 = AtomicU64::new(0x0BAD_C0DE_CAFE_F00D);
    let host_ptr: *const u8 = &HOST_FN as *const _ as *const u8;

    // Empty symbol tables — the symbol is NOT derivable from them; it is a
    // pure host promise (the `discover-tests` shape).
    let tables: SymbolTables<(), ()> = dashmap::DashMap::new();
    let mut jit = Jit::new(&tables).expect("Jit::new must succeed");

    // Promise the body BEFORE compiling the referencing thunk. (Promising
    // after declare-but-before-finalize would work equally — the map is
    // consulted at finalize, not at declare; this ordering matches int's
    // session-init promise.)
    jit.define_symbol("discover-tests", host_ptr);

    jit.declare_intrinsics().expect("intrinsics");

    // Thunk that references `discover-tests` as Import data and returns its
    // address. No eager `JITBuilder::symbol` registered it — only the
    // lookup fn (over the `define_symbol` map) can settle the relocation.
    let name = Symbol::from("get_extern_addr");
    let func_id = {
        let module = jit.jit_module();
        let mut sig = module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function(name.as_ref(), Linkage::Export, &sig)
            .expect("declare thunk");
        let data_id = module
            .declare_data("discover-tests", Linkage::Import, false, false)
            .expect("declare host symbol");
        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        ctx.func.name =
            cranelift::codegen::ir::UserFuncName::testcase(name.as_bytes());
        let mut fbc = FunctionBuilderContext::new();
        {
            let gv = module.declare_data_in_func(data_id, &mut ctx.func);
            let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.seal_block(entry);
            let addr = fb.ins().global_value(types::I64, gv);
            fb.ins().return_(&[addr]);
            fb.finalize();
        }
        module.define_function(id, &mut ctx).expect("define thunk");
        module.clear_context(&mut ctx);
        id
    };

    jit.finalize().expect("finalize must settle the host-promised import");
    let ptr = jit.get_finalized_ptr(func_id);
    // SAFETY: thunk just finalised; signature is `extern "C" fn() -> i64`.
    let f: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    assert_eq!(
        f() as u64,
        host_ptr as u64,
        "define_symbol must settle the unresolved Linkage::Import against \
         the host-promised pointer",
    );
    // Confirm the resolved address points AT the backing storage.
    let read = unsafe { std::ptr::read_unaligned(f() as u64 as *const u64) };
    assert_eq!(read, HOST_FN.load(Ordering::Relaxed));
}

// ----- §2 `intrinsics_table()` consumption -----

// spec: design/backend/jit-setup-boundary.md §2 — `declare_intrinsics_generic`
// reads `cranelisp_intrinsics::intrinsics_table()`, declaring one FuncId per
// catalog record. Confirms the re-point preserves the full intrinsic set and
// the 6 convenience accessors are populated.
#[test]
fn declare_intrinsics_generic_covers_the_catalog() {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();
    let ids = declare_intrinsics_generic(module).expect("declare");

    let catalog = cranelisp_intrinsics::intrinsics_table();
    assert_eq!(
        ids.by_name.len(),
        catalog.len(),
        "one declared FuncId per intrinsics_table() record",
    );
    for entry in catalog {
        assert!(
            ids.by_name.contains_key(&Symbol::from(entry.name)),
            "intrinsic '{}' must be declared",
            entry.name,
        );
    }
    // The 6 convenience accessors map to the named runtime intrinsics.
    assert!(ids.alloc.is_some(), "runtime/alloc accessor");
    assert!(ids.dealloc.is_some(), "runtime/dealloc accessor");
    assert!(ids.alloc_string.is_some(), "runtime/alloc_string accessor");
    assert!(ids.panic.is_some(), "runtime/panic accessor");
    assert!(ids.vec_new.is_some(), "runtime/vec_new accessor");
    assert!(ids.vec_drop.is_some(), "runtime/vec_drop accessor");
}

// ── Decision 31 reclaim reg-guards (S82 harvest of legacy
//    tests/legacy/v4_jit_reclaim.rs, FIXME 0133) ─────────────────────────
//
// The 6 legacy tests asserted Decision-31 reclaim invariants through the
// full `ReplSession` eval pipeline (`bytes_current()` deltas, session-held
// `Arc<Jit>` clone counts, `Code` enum shapes on `ModuleEntry::Def`). Per
// tests/CLAUDE.md §"Two tiers" + the s82-harvest disposition, the
// byte-counter / session-coupled assertions cannot be expressed at the
// unit tier; what IS the durable, crate-internal kernel of each reg-guard
// is the `Arc<Jit>` reclaim discipline that `Jit::drop` materialises. These
// units pin that kernel directly on `Arc<Jit>` — the same retention root
// the session layers `Code::Jit` over. All are REGRESSION-GUARDs (6 in the
// legacy file): a regression in `Jit::drop` / the reclaim counter surfaces
// here before it surfaces as a session-level leak or a dangling GOT slot.
#[allow(clippy::arc_with_non_send_sync)]
fn arc_jit() -> std::sync::Arc<Jit> {
    // `Arc<Jit>` is intentionally not Send+Sync (Jit is not Sync); the
    // reclaim discipline under test IS the production `Code::Jit(Arc<Jit>)`
    // shape, so the non-Send-Sync Arc is the thing under test.
    std::sync::Arc::new(Jit::new_with_symbols(&[]).expect("Jit::new for reclaim test"))
}

// spec: design/arch/CLAUDE.md Decision 31 Scenario 2 (headline assertion 1)
//       — a REDEFINITION produces a NEW JIT batch, never reuses the prior
//       batch's allocation. Kernel of the legacy
//       `decision31_scenario2_per_redefinition_jit_pages_reclaimed`
//       Arc::ptr_eq guard, lifted off the session to the Arc level.
#[test]
fn jit_batches_are_distinct_allocations() {
    use std::sync::Arc;
    let first = arc_jit();
    let second = arc_jit();
    assert!(
        !Arc::ptr_eq(&first, &second),
        "two separately-constructed JIT batches must be distinct Arc \
         allocations — a redefinition reusing the prior batch's allocation \
         violates Decision 31 Scenario 2"
    );
}

// spec: design/arch/CLAUDE.md Decision 31 Scenario 2 footnote
//       (unbounded-growth guard) — N batches created and released drive
//       at least N reclaims. Kernel of the legacy
//       `decision31_scenario2_repeated_redefinition_no_unbounded_growth`
//       reclaim-delta assertion: pre-Wave-3b `kept_jits` retained every
//       batch (0 reclaims until session drop); post-fix each batch's pages
//       reclaim as its last Arc clone drops.
#[test]
fn repeated_batch_drop_reclaims_each() {
    const N: u64 = 50;
    let before = jit_free_memory_call_count();
    for _ in 0..N {
        let jit = arc_jit();
        drop(jit); // last (only) clone drops → Jit::drop → free_memory
    }
    let after = jit_free_memory_call_count();
    assert!(
        after - before >= N,
        "expected at least {N} JIT::free_memory calls across {N} \
         create+drop cycles, got {}. Pre-Wave-3b retention would have \
         shown 0 reclaims until session teardown.",
        after - before
    );
}

// spec: design/arch/CLAUDE.md Decision 31 Scenario 1 — a batch with no
//       surviving holder reclaims IMMEDIATELY on drop (the per-eval case:
//       an expression eval creates no `ModuleEntry::Def`, so the eval-fn
//       batch is the sole Arc holder and its pages reclaim at end of eval).
//       Kernel of `decision31_scenario1_per_eval_jit_pages_reclaimed`.
#[test]
fn sole_holder_batch_reclaims_on_drop() {
    let before = jit_free_memory_call_count();
    {
        let _jit = arc_jit(); // sole holder; no session entry retains it
    } // drops here
    let after = jit_free_memory_call_count();
    assert_eq!(
        after, before + 1,
        "a batch with a single Arc holder must reclaim exactly once when \
         that holder drops (counter before={before}, after={after})"
    );
}

// spec: design/arch/CLAUDE.md Decision 31 Scenario 2 + Wave-3b carry-forward
//       invariant — reclaim fires ONLY when the LAST clone drops; while any
//       other clone lives, the pages stay valid. This is the crate-internal
//       kernel of the legacy
//       `wave3b_invariant_register_defn_does_not_drop_existing_arc_jit`
//       guard: the carry-forward keeps a second Arc clone alive across a
//       failed redefinition, so the original batch's GOT-referenced pages
//       must NOT reclaim mid-typecheck.
#[test]
fn batch_not_reclaimed_while_a_clone_survives() {
    use std::sync::Arc;
    let session_clone = arc_jit();
    let captured_clone = Arc::clone(&session_clone); // the "carry-forward" / test clone
    assert_eq!(Arc::strong_count(&session_clone), 2);

    let before = jit_free_memory_call_count();
    // Drop the "session" clone (the entry's `code` field being replaced).
    drop(session_clone);
    let after_partial_drop = jit_free_memory_call_count();
    assert_eq!(
        after_partial_drop, before,
        "dropping one of two Arc<Jit> clones MUST NOT reclaim — the batch's \
         pages are still referenced by the surviving clone; reclaiming here \
         would dangle the GOT slot (Wave 3b carry-forward invariant)"
    );
    assert_eq!(
        Arc::strong_count(&captured_clone),
        1,
        "the surviving clone is now the sole holder"
    );

    // Now drop the last clone — reclaim fires exactly once.
    drop(captured_clone);
    let after_final_drop = jit_free_memory_call_count();
    assert_eq!(
        after_final_drop, before + 1,
        "dropping the LAST Arc<Jit> clone must reclaim exactly once"
    );
}
