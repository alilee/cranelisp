use super::*;

// spec: design/backend/module-caching.md §9 — linker symbol registration and lookup
#[test]
fn test_linker_register_and_lookup() {
    let mut linker = Linker::new().unwrap();
    let addr = 0x1234usize as *const u8;
    linker.register_symbol("runtime/alloc", addr);
    assert_eq!(linker.get_symbol("runtime/alloc").ok(), Some(addr));
}

// spec: design/backend/module-caching.md §9 — linker returns LinkerError::SymbolNotFound
//       for unknown symbols (Decision 37; typed-error contract).
#[test]
fn test_linker_unknown_symbol() {
    let linker = Linker::new().unwrap();
    let result = linker.get_symbol("nonexistent");
    assert!(matches!(result, Err(LinkerError::SymbolNotFound { .. })));
}

// spec: design/backend/module-caching.md §9 — linker creation succeeds
#[test]
fn test_linker_new() {
    let linker = Linker::new().unwrap();
    assert!(linker.symbols.is_empty());
}

// spec: design/arch/CLAUDE.md Decision 23 — Sprint 58 Wave 2 regression
// guard. Cranelift emits `ARM64_RELOC_GOT_LOAD_PAGE21` /
// `ARM64_RELOC_GOT_LOAD_PAGEOFF12` relocations when CLIF references an
// `Linkage::Import` data symbol (such as `__cranelisp_got_{M}` for cross-
// module GOT-base references) via `global_value`. The cache `Linker` MUST
// resolve these by allocating an in-process slot containing the
// registered symbol's address and patching the relocations to point at
// the slot (not the symbol). This test synthesizes an .o with such a
// reference, loads it via the linker, and asserts the slot contains the
// registered symbol's address.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn linker_resolves_arm64_got_load_relocations() {
    use cranelift::codegen::Context;
    use cranelift::codegen::ir::{Function, UserFuncName, types};
    use cranelift::prelude::{
        AbiParam, FunctionBuilder, FunctionBuilderContext, InstBuilder, Signature,
    };
    use cranelift_module::{Linkage, Module};
    use cranelift_object::{ObjectBuilder, ObjectModule};

    // Build an aarch64 PIC ISA — same as the cache build path.
    let isa = crate::cache::object::build_isa(true).unwrap();
    let call_conv = isa.default_call_conv();
    let builder = ObjectBuilder::new(
        isa,
        "got_load_reloc_test",
        cranelift_module::default_libcall_names(),
    )
    .unwrap();
    let mut module = ObjectModule::new(builder);

    // Declare an Import data symbol — the canonical case that triggers
    // GOT_LOAD relocations on aarch64 macOS.
    let import_data = module
        .declare_data("__cranelisp_got_imported", Linkage::Import, false, false)
        .unwrap();

    // Declare a function `get_got_base` that returns the address of the
    // import data symbol (mirroring how compile_to_module's
    // `emit_got_indirect_call_via_data_id` emits the slab base — the
    // symbol address IS the slab base, no extra pointer-cell deref).
    let mut sig = Signature::new(call_conv);
    sig.returns.push(AbiParam::new(types::I64));
    let func_id = module
        .declare_function("get_got_base", Linkage::Export, &sig)
        .unwrap();

    let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig.clone());
    let mut fbc = FunctionBuilderContext::new();
    {
        let import_gv = module.declare_data_in_func(import_data, &mut func);
        let mut fb = FunctionBuilder::new(&mut func, &mut fbc);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.seal_block(entry);
        let addr = fb.ins().symbol_value(types::I64, import_gv);
        fb.ins().return_(&[addr]);
        fb.finalize();
    }

    let mut ctx = Context::for_function(func);
    module.define_function(func_id, &mut ctx).unwrap();

    let product = module.finish();
    let bytes = product.emit().unwrap();

    // Sanity: the synthesised .o must contain GOT_LOAD relocations against
    // our import symbol — otherwise the test would not exercise the new
    // code path.
    {
        use ::object::{Object, ObjectSection, ObjectSymbol, RelocationFlags, RelocationTarget};
        let parsed = ::object::File::parse(&*bytes).unwrap();
        let text = parsed
            .section_by_name("__text")
            .or_else(|| parsed.section_by_name(".text"))
            .expect("text section must exist");
        let mut got_load_count = 0usize;
        for (_off, reloc) in text.relocations() {
            if let RelocationTarget::Symbol(sym_idx) = reloc.target() {
                let sym = parsed.symbol_by_index(sym_idx).unwrap();
                let nm = sym.name().unwrap_or("");
                let clean = nm.strip_prefix('_').unwrap_or(nm);
                if clean == "__cranelisp_got_imported"
                    && let RelocationFlags::MachO { r_type, .. } = reloc.flags()
                    && (r_type == macho_arm64::ARM64_RELOC_GOT_LOAD_PAGE21
                        || r_type == macho_arm64::ARM64_RELOC_GOT_LOAD_PAGEOFF12)
                {
                    got_load_count += 1;
                }
            }
        }
        assert!(
            got_load_count >= 2,
            "synthesised .o must emit at least one GOT_LOAD_PAGE21 + \
             GOT_LOAD_PAGEOFF12 pair against the Import symbol so this \
             test exercises the new code path; got {got_load_count}"
        );
    }

    // Use the address of a stable heap allocation as the registered
    // symbol value. The slot will be initialised with this address.
    let stable: Box<u64> = Box::new(0xDEAD_BEEF_F00D_CAFEu64);
    let stable_ptr: *const u64 = &*stable;
    let mut linker = Linker::new().unwrap();
    linker.register_symbol("__cranelisp_got_imported", stable_ptr as *const u8);

    // Load the synthesised .o — this MUST NOT error on the GOT_LOAD relocs.
    linker
        .load_object("got_load_reloc_test", &bytes)
        .expect("linker must accept GOT_LOAD relocations and resolve them via in-process slots");

    // Verify the linker allocated a GOT slot for the symbol and the slot
    // contains the registered address (the slot is the indirection that
    // the patched ADRP+LDR will load through at runtime).
    let slot_addr = *linker
        .got_slots
        .get("__cranelisp_got_imported")
        .expect("linker must allocate a GOT slot for the GOT_LOAD-referenced symbol");
    let stored = unsafe { *(slot_addr as *const u64) };
    assert_eq!(
        stored, stable_ptr as u64,
        "GOT slot must hold the registered symbol address; got {:#x}",
        stored
    );

    // Keep `stable` alive until after the assertion (drop runs at end of fn).
    drop(stable);
}

// spec: design/backend/cache-repl-loads-triage.md — Sprint 59 Wave 1 C-ii
// regression guard. Cranelift emits `ARM64_RELOC_GOT_LOAD_*` relocations
// not only against `Linkage::Import` data symbols but also against local
// `.L*` data labels it synthesises for string-literal constants
// (e.g. panic messages in trait-method dispatchers). Those local symbols
// live in the per-object `local_symbols` map — not in `self.defined_symbols`
// or `self.symbols`. `ensure_got_slot` must accept the pre-resolved address
// from its caller rather than re-looking-up the symbol by name, so that
// GOT-slot allocation succeeds for local data labels too. Extends the
// Decision-23 regression-guard coverage to `.L*` locals.
#[test]
fn ensure_got_slot_accepts_preresolved_local_symbol_address() {
    let mut linker = Linker::new().unwrap();
    // Simulate a `.L`-local data symbol's address resolved by the outer
    // relocation loop from a per-object `local_symbols` map. The symbol
    // is NOT registered via `register_symbol` and is NOT in
    // `defined_symbols` — exactly the condition that caused the
    // pre-fix `undefined symbol` error.
    let stable: Box<u64> = Box::new(0xFEED_FACE_DEAD_BEEFu64);
    let stable_ptr: *const u64 = &*stable;
    let pre_resolved_addr = stable_ptr as usize;

    assert!(
        !linker.defined_symbols.contains_key(".Ldata0"),
        "precondition: .Ldata0 must not be pre-registered (that's the whole bug shape)"
    );
    assert!(
        !linker.symbols.contains_key(".Ldata0"),
        "precondition: .Ldata0 must not be in the external-symbol table either"
    );

    let slot_addr = linker
        .ensure_got_slot(".Ldata0", pre_resolved_addr)
        .expect("ensure_got_slot must accept a pre-resolved local symbol address");
    let stored = unsafe { *(slot_addr as *const u64) };
    assert_eq!(
        stored, pre_resolved_addr as u64,
        "GOT slot must hold the caller-supplied address"
    );

    // Second call for the same symbol returns the same slot (idempotent).
    let slot_addr2 = linker
        .ensure_got_slot(".Ldata0", pre_resolved_addr)
        .expect("second call must return cached slot");
    assert_eq!(slot_addr, slot_addr2, "repeat calls return the same slot");

    drop(stable);
}

// spec: design/arch/CLAUDE.md Decision 23 + Sprint 60 Wave 2 Step A.3
// (single-GOT convergence). When a cached `.o` file is loaded,
// `load_data_sections` must NOT register the `.o`'s own
// `__cranelisp_got_{M}` export into `self.defined_symbols` — the
// authoritative GOT slab base is the in-process `SymbolTable[M].got`
// registered externally via `register_symbol`. Allowing the `.o`'s own
// data address to shadow the externally-registered symbol is the
// dual-GOT breach reproduced by `tests/sprint60_reduction.rs`. This
// unit test synthesises an `.o` whose data section exports
// `__cranelisp_got_imported`, loads it alongside an external
// registration, and asserts that the GOT slot is initialised to the
// externally-registered address — not to the `.o`'s own data section.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn loaded_object_does_not_shadow_externally_registered_got_symbol() {
    use cranelift::codegen::Context;
    use cranelift::codegen::ir::{Function, UserFuncName, types};
    use cranelift::prelude::{
        AbiParam, FunctionBuilder, FunctionBuilderContext, InstBuilder, Signature,
    };
    use cranelift_module::{DataDescription, Linkage, Module};
    use cranelift_object::{ObjectBuilder, ObjectModule};

    let isa = crate::cache::object::build_isa(true).unwrap();
    let call_conv = isa.default_call_conv();
    let builder = ObjectBuilder::new(
        isa,
        "got_convergence_test",
        cranelift_module::default_libcall_names(),
    )
    .unwrap();
    let mut module = ObjectModule::new(builder);

    // Define the GOT data symbol as Export (the shape a compiled
    // `.o` file has for its own-module GOT — the `--link` path needs
    // this symbol exported so the system linker can resolve it).
    let got_data = module
        .declare_data("__cranelisp_got_imported", Linkage::Export, false, false)
        .unwrap();
    let mut desc = DataDescription::new();
    // 16 bytes = 2 slots, zero-filled (no relocations) — simulates
    // the worst case where the `.o`'s own data section is never
    // relocated (if we trust it we segfault on indirect call).
    desc.define(vec![0u8; 16].into_boxed_slice());
    module.define_data(got_data, &desc).unwrap();

    // A tiny function so the `.o` is non-empty.
    let mut sig = Signature::new(call_conv);
    sig.returns.push(AbiParam::new(types::I64));
    let func_id = module
        .declare_function("unused", Linkage::Export, &sig)
        .unwrap();
    let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig.clone());
    let mut fbc = FunctionBuilderContext::new();
    {
        let mut fb = FunctionBuilder::new(&mut func, &mut fbc);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.seal_block(entry);
        let zero = fb.ins().iconst(types::I64, 0);
        fb.ins().return_(&[zero]);
        fb.finalize();
    }
    let mut ctx = Context::for_function(func);
    module.define_function(func_id, &mut ctx).unwrap();

    let bytes = module.finish().emit().unwrap();

    // Register the authoritative GOT base externally FIRST, just as
    // `src/worker.rs::load_cached_module_via_linker` does.
    let authoritative: Box<[u64; 2]> = Box::new([0xAAAA_AAAA_AAAA_AAAA, 0xBBBB_BBBB_BBBB_BBBB]);
    let authoritative_ptr = authoritative.as_ptr() as *const u8;
    let mut linker = Linker::new().unwrap();
    linker.register_symbol("__cranelisp_got_imported", authoritative_ptr);

    linker
        .load_object("got_convergence_test", &bytes)
        .expect("linker must accept the .o");

    // Convergence invariant: the loaded `.o`'s own
    // `__cranelisp_got_imported` data-section address must NOT
    // shadow the externally-registered authoritative GOT base.
    assert!(
        !linker
            .defined_symbols
            .contains_key("__cranelisp_got_imported"),
        "loading a .o must NOT insert __cranelisp_got_* into \
         defined_symbols; the externally-registered SymbolTable.got \
         base is the sole authoritative resolver (single-GOT)"
    );
    // `get_symbol` must return the externally-registered address.
    assert_eq!(
        linker.get_symbol("__cranelisp_got_imported").ok(),
        Some(authoritative_ptr),
        "get_symbol for __cranelisp_got_* must return the \
         externally-registered SymbolTable GOT base"
    );

    drop(authoritative);
}
