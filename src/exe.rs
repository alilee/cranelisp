// Standalone executable generation — binary crate orchestration.
//
// Validates `main`, collects `.o` paths, locates the bundle library and
// platform rlibs, and invokes the system linker. The Cranelift-dependent
// startup stub generation lives in `cranelisp-backend::exe`.
//
// See design/backend/executable-generation.md for the full design.
//
// Owned by /backend (design, startup stub, main validation).
// Wired into the CLI by /int.

use std::path::{Path, PathBuf};
use std::process::Command;

use cranelisp_types::{ErrorLocation, 
    CranelispError, ModuleEntry, ModuleFullPath, Span, Type,
};

/// Generate a startup `.o` that defines `start` (exported, referenced by the
/// linker via `-e _start`) which initializes platforms, calls `main()`,
/// optionally runs the IO trampoline, and calls `exit()`.
///
/// S76 §4.4 (/arch RULED, Phase-2 Q1): int owns startup-object emission — the
/// `--link` `_main`/`start` alias is int's link-orchestration (BC §3 invariant
/// 7), NOT a backend boundary. The body was relocated here from the backend's
/// `pub(crate) generate_startup_object`; it uses Cranelift directly (no
/// codegen-from-`symbol_tables`), so it does not belong behind
/// `compile_to_module`. Mirrors the existing `generate_main_alias_object`.
///
/// # Arguments
/// * `platform_manifest_names` — symbol names for platform manifest functions
///   (e.g., `["cranelisp_platform_manifest"]`). Empty if no platforms.
/// * `main_returns_io` — if true, inserts a `cranelisp_run_io` call to force
///   the IO task tree before extracting the exit code.
/// * `entry_fn_name` — the user-main symbol the stub imports and calls. macOS
///   `"main"`; Linux `"cranelisp_user_main"` (the alias `.o`'s Export). Read
///   from `host_entry_symbols()` at the call site (design §11.3).
/// * `stub_entry_symbol` — the symbol this stub exports as the executable entry.
///   macOS `"start"` (linked `-e _start`); Linux `"main"` (crt calls it, so the
///   stub IS C `main` — glibc/TLS/malloc are initialised before it runs, design
///   §11.3). Read from `host_entry_symbols()` at the call site.
/// * `platform_layout_checks` — per-platform layout-hash checks to bake into the
///   `start` stub (platform-interface.md §5.5.4 `--link` gate). For each check
///   the stub declares the rlib's `__cranelisp_layout_hash_<name>` as imported
///   data, bakes the compiler-computed expected hash + name as `.rodata`, and
///   calls `cranelisp_check_layout_hash(linked, expected, name)` before `main`
///   — a stale platform builds but aborts at process start with rebuild
///   guidance. Empty = no checks (the as-built no-platform path).
pub fn generate_startup_object(
    platform_manifest_names: &[String],
    main_returns_io: bool,
    entry_fn_name: &str,
    stub_entry_symbol: &str,
    platform_layout_checks: &[cranelisp_backend::exe::PlatformLayoutCheck],
) -> Result<Vec<u8>, CranelispError> {
    use cranelift::prelude::*;
    use cranelisp_backend::cranelift_module::{
        default_libcall_names, DataDescription, Linkage, Module,
    };
    use cranelisp_backend::cranelift_object::{ObjectBuilder, ObjectModule};

    // Bake a NUL-terminated rodata string and return its DataId (for the
    // expected-hash + platform-name constants the layout-hash gate reads).
    fn define_cstr_data(
        obj_module: &mut ObjectModule,
        sym: &str,
        text: &str,
    ) -> Result<cranelisp_backend::cranelift_module::DataId, CranelispError> {
        let id = obj_module
            .declare_data(sym, Linkage::Local, false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare {sym}: {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        let mut desc = DataDescription::new();
        let mut bytes = text.as_bytes().to_vec();
        bytes.push(0);
        desc.define(bytes.into_boxed_slice());
        obj_module
            .define_data(id, &desc)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define {sym}: {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        Ok(id)
    }

    let isa = cranelisp_backend::build_isa(true)?;

    let obj_builder = ObjectBuilder::new(isa, "cranelisp_startup", default_libcall_names())
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to create ObjectBuilder: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    let mut obj_module = ObjectModule::new(obj_builder);

    // Declare entry function as imported (user's main function, returns i64).
    let mut main_sig = obj_module.make_signature();
    main_sig.returns.push(AbiParam::new(types::I64));
    let main_func_id = obj_module
        .declare_function(entry_fn_name, Linkage::Import, &main_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare {entry_fn_name}: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    // Declare `cranelisp_run_io` as imported (IO trampoline).
    let run_io_func_id = if main_returns_io {
        let mut run_io_sig = obj_module.make_signature();
        run_io_sig.params.push(AbiParam::new(types::I64));
        run_io_sig.returns.push(AbiParam::new(types::I64));
        Some(
            obj_module
                .declare_function("cranelisp_run_io", Linkage::Import, &run_io_sig)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare cranelisp_run_io: {e}"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?,
        )
    } else {
        None
    };

    // Declare `exit` as imported (libc, takes i32).
    let mut exit_sig = obj_module.make_signature();
    exit_sig.params.push(AbiParam::new(types::I32));
    let exit_func_id = obj_module
        .declare_function("exit", Linkage::Import, &exit_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare exit: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    // Declare `cranelisp_init_primitives` as imported (zero-arg). The startup
    // stub MUST call this unconditionally before user code runs (FIXME 0280):
    // it forces `cranelisp_primitives::PRIMITIVES_TABLE`'s `LazyLock`, which
    // populates the exported `__cranelisp_got_primitives` static slab with the
    // extern primitives' fn addresses. Without it the slab slots stay null and
    // the first GOT-indirect extern-primitive dispatch jumps to null (SIGSEGV).
    // `cranelisp_init_platform` ALSO forces it (so platform programs were
    // covered), but a no-platform program calling an extern primitive
    // (`(str-len (str-concat …))`) reaches user code with an unpopulated GOT
    // unless we call it here directly. `LazyLock::force` is idempotent.
    let init_primitives_sig = obj_module.make_signature();
    let init_primitives_func_id = obj_module
        .declare_function(
            "cranelisp_init_primitives",
            Linkage::Import,
            &init_primitives_sig,
        )
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare cranelisp_init_primitives: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    // Declare the layout-hash check intrinsic + per-platform data symbols
    // (platform-interface.md §5.5.4 `--link` gate). Mirrors backend's
    // `generate_startup_object_checked` (int owns the startup `.o` emission, BC
    // §3 invariant 7). For each check: an imported `__cranelisp_layout_hash_<name>`
    // (the rlib's embedded hash), a baked expected-hash cstring, a baked name
    // cstring; the compare-and-abort is `cranelisp_check_layout_hash`.
    struct LayoutCheckIds {
        check_fn: cranelisp_backend::cranelift_module::FuncId,
        per_platform: Vec<(
            cranelisp_backend::cranelift_module::DataId,
            cranelisp_backend::cranelift_module::DataId,
            cranelisp_backend::cranelift_module::DataId,
        )>,
    }
    let layout_check_ids = if platform_layout_checks.is_empty() {
        None
    } else {
        let mut sig = obj_module.make_signature();
        sig.params.push(AbiParam::new(types::I64)); // linked hash ptr
        sig.params.push(AbiParam::new(types::I64)); // expected hash ptr
        sig.params.push(AbiParam::new(types::I64)); // platform name ptr
        let check_fn = obj_module
            .declare_function("cranelisp_check_layout_hash", Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare cranelisp_check_layout_hash: {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        let mut per_platform = Vec::with_capacity(platform_layout_checks.len());
        for check in platform_layout_checks {
            let linked_sym = format!("__cranelisp_layout_hash_{}", check.name);
            let linked_id = obj_module
                .declare_data(&linked_sym, Linkage::Import, false, false)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare {linked_sym}: {e}"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?;
            let expected_id = define_cstr_data(
                &mut obj_module,
                &format!("__cranelisp_expected_hash_{}", check.name),
                &check.expected_hash,
            )?;
            let name_id = define_cstr_data(
                &mut obj_module,
                &format!("__cranelisp_layout_name_{}", check.name),
                &check.name,
            )?;
            per_platform.push((linked_id, expected_id, name_id));
        }
        Some(LayoutCheckIds { check_fn, per_platform })
    };

    // Declare `cranelisp_init_platform` as imported (if platforms exist).
    let init_func_id = if !platform_manifest_names.is_empty() {
        let mut init_sig = obj_module.make_signature();
        init_sig.params.push(AbiParam::new(types::I64));
        Some(
            obj_module
                .declare_function("cranelisp_init_platform", Linkage::Import, &init_sig)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare cranelisp_init_platform: {e}"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?,
        )
    } else {
        None
    };

    // Declare each platform manifest function as imported.
    let mut manifest_func_ids = Vec::new();
    for manifest_name in platform_manifest_names {
        let manifest_sig = obj_module.make_signature();
        let fid = obj_module
            .declare_function(manifest_name, Linkage::Import, &manifest_sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare {manifest_name}: {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        manifest_func_ids.push(fid);
    }

    // Define the entry stub (exported). macOS exports `start` (linked
    // `-e _start`); Linux exports `main` (crt calls it — the stub IS C `main`,
    // so glibc/TLS/malloc are up before any user code runs; design §11.3).
    let start_sig = obj_module.make_signature();
    let start_func_id = obj_module
        .declare_function(stub_entry_symbol, Linkage::Export, &start_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare {stub_entry_symbol}: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    let mut func = cranelift::codegen::ir::Function::with_name_signature(
        cranelift::codegen::ir::UserFuncName::user(0, start_func_id.as_u32()),
        start_sig,
    );

    let mut func_ctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut func, &mut func_ctx);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // 0. Populate the primitives GOT slab before anything else (FIXME 0280).
        let init_primitives_ref =
            obj_module.declare_func_in_func(init_primitives_func_id, builder.func);
        builder.ins().call(init_primitives_ref, &[]);

        // 1. Initialize platforms before calling main.
        if let Some(init_fid) = init_func_id {
            let init_ref = obj_module.declare_func_in_func(init_fid, builder.func);
            for &manifest_fid in &manifest_func_ids {
                let manifest_ref = obj_module.declare_func_in_func(manifest_fid, builder.func);
                let addr = builder.ins().func_addr(types::I64, manifest_ref);
                builder.ins().call(init_ref, &[addr]);
            }
        }

        // 1.5. Layout-hash gate (platform-interface.md §5.5.4 `--link`): compare
        // the compiler-computed expected hash against the rlib's statically
        // linked `__cranelisp_layout_hash_<name>` and abort on mismatch — before
        // main runs, so a stale platform refuses at process start.
        if let Some(ref ids) = layout_check_ids {
            let check_ref = obj_module.declare_func_in_func(ids.check_fn, builder.func);
            for &(linked_id, expected_id, name_id) in &ids.per_platform {
                let linked_gv = obj_module.declare_data_in_func(linked_id, builder.func);
                let expected_gv = obj_module.declare_data_in_func(expected_id, builder.func);
                let name_gv = obj_module.declare_data_in_func(name_id, builder.func);
                let linked_ptr = builder.ins().global_value(types::I64, linked_gv);
                let expected_ptr = builder.ins().global_value(types::I64, expected_gv);
                let name_ptr = builder.ins().global_value(types::I64, name_gv);
                builder
                    .ins()
                    .call(check_ref, &[linked_ptr, expected_ptr, name_ptr]);
            }
        }

        // 2. Call main().
        let main_ref = obj_module.declare_func_in_func(main_func_id, builder.func);
        let call_inst = builder.ins().call(main_ref, &[]);
        let main_result = builder.inst_results(call_inst)[0];

        // 3. If main returns IO, force the task tree via trampoline.
        let ret_val = if let Some(run_io_fid) = run_io_func_id {
            let run_io_ref = obj_module.declare_func_in_func(run_io_fid, builder.func);
            let run_inst = builder.ins().call(run_io_ref, &[main_result]);
            builder.inst_results(run_inst)[0]
        } else {
            main_result
        };

        // 4. Truncate i64 -> i32 for exit code.
        let exit_code = builder.ins().ireduce(types::I32, ret_val);

        // 5. Call exit(code).
        let exit_ref = obj_module.declare_func_in_func(exit_func_id, builder.func);
        builder.ins().call(exit_ref, &[exit_code]);

        // Unreachable after exit, but Cranelift needs a block terminator.
        builder.ins().trap(TrapCode::user(1).unwrap());

        builder.finalize();
    }

    let mut ctx = cranelift::codegen::Context::for_function(func);
    obj_module
        .define_function(start_func_id, &mut ctx)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define {stub_entry_symbol}: {e:?}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    let product = obj_module.finish();
    product.emit().map_err(|e| CranelispError::CodegenError {
        message: format!("failed to emit startup object: {e}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })
}

// ── Main return type ────────────────────────────────────────────────────

/// Whether `main` returns IO (needs trampoline) or Int (direct exit code).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MainReturnKind {
    Int,
    Io,
}

/// Validate that the entry module exports a `main` function with an acceptable
/// type signature: `() -> Int` or `() -> IO _`.
///
/// Returns the return kind so the startup stub can conditionally include the
/// IO trampoline.
pub fn validate_main(entry_symbols: &crate::code::SessionSymbolTable) -> Result<MainReturnKind, CranelispError> {
    let entry = entry_symbols.get("main").ok_or_else(|| {
        CranelispError::CodegenError {
            message: "entry module has no 'main' function".to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    })?;

    match entry {
        ModuleEntry::Def { scheme, .. } => classify_main_return_type(&scheme.ty),
        _ => Err(CranelispError::CodegenError {
            message: "'main' in entry module is not a function definition".to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

/// Classify the return type of `main`.
fn classify_main_return_type(ty: &Type) -> Result<MainReturnKind, CranelispError> {
    match ty {
        Type::Fn(params, ret) if params.is_empty() => match ret.as_ref() {
            Type::Int => Ok(MainReturnKind::Int),
            Type::ADT(name, _) if name.name.as_ref() == "IO" => Ok(MainReturnKind::Io),
            other => Err(CranelispError::CodegenError {
                message: format!(
                    "main must return Int or IO, found: {}",
                    type_display_brief(other)
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }),
        },
        _ => Err(CranelispError::CodegenError {
            message: format!(
                "main must be a zero-argument function, found: {}",
                type_display_brief(ty)
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

/// Brief type display for error messages.
fn type_display_brief(ty: &Type) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::Float => "Float".to_string(),
        Type::String => "String".to_string(),
        Type::Var(_) => "<inferred>".to_string(),
        Type::TyConApp(_, _) => "<type-app>".to_string(),
        Type::ADT(name, args) => {
            if args.is_empty() {
                name.to_string()
            } else {
                format!(
                    "({} {})",
                    name,
                    args.iter()
                        .map(type_display_brief)
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
        }
        Type::Fn(params, ret) => {
            let param_strs: Vec<String> = params.iter().map(type_display_brief).collect();
            format!(
                "(Fn [{}] {})",
                param_strs.join(" "),
                type_display_brief(ret)
            )
        }
    }
}

// ── `_main` entry-point alias (Decision 36 `--link` exception) ──────────

/// Generate a small alias `.o` defining `main` as `Linkage::Export`, body =
/// GOT-indirect tail-call into the entry module's `__cranelisp_got_{M}`
/// data symbol at the slot allocated for `main`.
///
/// This satisfies Decision 36's "`--link` entry point exception": every
/// user-defined function is declared bare-`Linkage::Local` by
/// `compile_to_module`, but the system linker requires `_main` (or the
/// configured entry stub's referenced name) as a globally-visible symbol.
/// Rather than punching a per-module-name special case back into
/// `compile_to_module`, the `--link` layer emits a separate alias `.o` that
/// tail-calls through the GOT — the same indirection mechanism every
/// cross-module call uses (Decision 23 + 31). The entry module's
/// `__cranelisp_got_{M}` data symbol is `Linkage::Export` per the
/// Bug B fix in `define_module_got_data` (Sprint 58 Wave 2 / Decision 23),
/// so the alias `.o` can resolve it at link time.
///
/// # Arguments
/// * `entry_module` — module path of the entry module (e.g. `zero`, `main`,
///   `hello`). Used to compute the GOT data-symbol name.
/// * `main_got_slot` — the GOT slot index that the entry module's symbol
///   table allocated for `main`. Read off
///   `symbol_tables[entry_module].symbols["main"].got_slot.unwrap()`.
/// * `user_main_symbol` — the name this alias exports. macOS `"main"` (the
///   stub's import); Linux `"cranelisp_user_main"`, renamed to avoid colliding
///   with the C `main` the Linux stub itself exports (design §11.3). Read from
///   `host_entry_symbols()` at the call site.
///
/// # Returns
/// Raw bytes of a relocatable ELF/Mach-O `.o` file containing one Export symbol
/// (`user_main_symbol`) whose body loads
/// `__cranelisp_got_{entry_module}[main_got_slot]` and tail-calls the resulting
/// function pointer.
pub fn generate_main_alias_object(
    entry_module: &ModuleFullPath,
    main_got_slot: usize,
    user_main_symbol: &str,
) -> Result<Vec<u8>, CranelispError> {
    use cranelift::prelude::*;
    use cranelisp_backend::cranelift_module::{default_libcall_names, Linkage, Module};
    use cranelisp_backend::cranelift_object::{ObjectBuilder, ObjectModule};

    let isa = cranelisp_backend::build_isa(true)?;
    let obj_builder = ObjectBuilder::new(
        isa,
        "cranelisp_main_alias",
        default_libcall_names(),
    )
    .map_err(|e| CranelispError::CodegenError {
        message: format!("failed to create ObjectBuilder for main alias: {e}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })?;
    let mut obj_module = ObjectModule::new(obj_builder);

    // Declare the per-entry-module GOT data symbol as Linkage::Import.
    // The entry module's `.o` defines this symbol as Export (per Bug B fix
    // in `define_module_got_data` — Sprint 58 Wave 2 / Decision 23).
    let got_name = cranelisp_types::got_data_symbol_name(entry_module);
    let got_data_id = obj_module
        .declare_data(&got_name, Linkage::Import, false, false)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare {got_name} as Import: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    // Declare the user-main alias as Linkage::Export. The startup stub's
    // import of the user-main symbol resolves against this. macOS: `main`;
    // Linux: `cranelisp_user_main` (the C `main` is the stub itself).
    let mut main_sig = obj_module.make_signature();
    main_sig.returns.push(AbiParam::new(types::I64));
    let main_func_id = obj_module
        .declare_function(user_main_symbol, Linkage::Export, &main_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare {user_main_symbol} alias as Export: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    let mut func = cranelift::codegen::ir::Function::with_name_signature(
        cranelift::codegen::ir::UserFuncName::user(0, main_func_id.as_u32()),
        main_sig,
    );

    let mut func_ctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut func, &mut func_ctx);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Load the GOT base address.
        let got_global = obj_module.declare_data_in_func(got_data_id, builder.func);
        let got_base = builder.ins().symbol_value(types::I64, got_global);

        // Load the function pointer at slot `main_got_slot * 8`.
        let slot_offset: i32 = (main_got_slot * 8).try_into().map_err(|_| {
            CranelispError::CodegenError {
                message: format!(
                    "main GOT slot offset overflows i32 for slot {main_got_slot}"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
        let fn_ptr = builder.ins().load(
            types::I64,
            cranelift::codegen::ir::MemFlags::trusted(),
            got_base,
            slot_offset,
        );

        // Tail-call via `call_indirect`. The signature: `() -> i64`.
        let mut ind_sig = obj_module.make_signature();
        ind_sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = builder.import_signature(ind_sig);
        let call = builder.ins().call_indirect(sig_ref, fn_ptr, &[]);
        let result = builder.inst_results(call)[0];
        builder.ins().return_(&[result]);
        builder.finalize();
    }

    let mut ctx = cranelift::codegen::Context::for_function(func);
    obj_module
        .define_function(main_func_id, &mut ctx)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define {user_main_symbol} alias: {e:?}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    let product = obj_module.finish();
    product.emit().map_err(|e| CranelispError::CodegenError {
        message: format!("failed to emit main alias object: {e}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })
}

/// Look up the `main` GOT slot for the given entry module's symbol table.
///
/// Returns the slot index pinned at typecheck time. Errors if `main` is
/// missing or has no slot allocated (defensive — `validate_main` should
/// have caught the missing case).
pub fn entry_main_got_slot(entry_table: &crate::code::SessionSymbolTable) -> Result<usize, CranelispError> {
    let entry = entry_table.get("main").ok_or_else(|| {
        CranelispError::CodegenError {
            message: "entry module has no 'main' function (alias generation)".to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    })?;
    match entry {
        ModuleEntry::Def { got_slot: Some(slot), .. } => Ok(*slot),
        ModuleEntry::Def { got_slot: None, .. } => Err(CranelispError::CodegenError {
            message: "entry module's 'main' has no GOT slot — typecheck did \
                      not pin a slot index".to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
        _ => Err(CranelispError::CodegenError {
            message: "entry module's 'main' is not a Def entry".to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

// ── Linker configuration ────────────────────────────────────────────────

/// Which native linker driver to invoke (design §11.6).
///
/// `AppleLd` drives bare `ld` (ld64) on macOS; `Cc` drives the `cc` (gcc)
/// driver on Linux so the crt objects, dynamic-linker path, default search
/// paths, and libc are supplied by the driver (design §11.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LinkDriver {
    AppleLd,
    Cc,
}

/// Host-dispatched linker configuration (design §11.6).
///
/// Carries the entry strategy (which symbol the stub exports as the entry, and
/// what the user-main alias is named) and the driver. macOS keeps its custom
/// crt-bypassing entry (`start` / `main`, Apple `ld`); Linux routes through crt
/// by emitting the stub as C `main`, so the user-main alias is renamed to
/// `cranelisp_user_main` to avoid colliding with the C `main` (design §11.3).
struct LinkerConfig {
    driver: LinkDriver,
    /// The symbol the startup stub exports as the entry. macOS: `"start"`
    /// (linked `-e _start`). Linux: `"main"` (crt calls it).
    stub_entry_symbol: &'static str,
    /// The user-main alias export / the stub's import of user main. macOS:
    /// `"main"`. Linux: `"cranelisp_user_main"`.
    user_main_symbol: &'static str,
    // macOS-only fields (None on Linux — the `cc` driver supplies these):
    arch: Option<&'static str>,
    /// (platform, min_version, sdk_version) — macOS `-platform_version` triplet.
    platform_triplet: Option<(&'static str, &'static str, &'static str)>,
}

impl LinkerConfig {
    /// Configuration for the current host. macOS aarch64 → Apple `ld`; Linux
    /// aarch64 → `cc` driver (design §11.6).
    fn for_host() -> Result<Self, CranelispError> {
        match (cfg!(target_arch = "aarch64"), std::env::consts::OS) {
            (true, "macos") => Ok(LinkerConfig {
                driver: LinkDriver::AppleLd,
                stub_entry_symbol: "start",
                user_main_symbol: "main",
                arch: Some("arm64"),
                platform_triplet: Some(("macos", "14.0", "14.0")),
            }),
            (true, "linux") => Ok(LinkerConfig {
                driver: LinkDriver::Cc,
                stub_entry_symbol: "main",
                user_main_symbol: "cranelisp_user_main",
                arch: None,
                platform_triplet: None,
            }),
            _ => Err(CranelispError::CodegenError {
                message: "standalone executable generation is only supported on \
                          aarch64 macOS and aarch64 Linux"
                    .to_string(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }),
        }
    }
}

/// The startup-stub export symbol and the user-main alias symbol for the host
/// (design §11.3). Read by the call site (`session_v4.rs`) so the stub's import
/// of user main and the alias's export use the host-correct names.
///
/// Returns `(stub_entry_symbol, user_main_symbol)`.
pub fn host_entry_symbols() -> Result<(&'static str, &'static str), CranelispError> {
    let config = LinkerConfig::for_host()?;
    Ok((config.stub_entry_symbol, config.user_main_symbol))
}

// ── Link executable ─────────────────────────────────────────────────────

/// Link module `.o` files and startup `.o` with the runtime bundle
/// and platform rlibs into a native executable.
///
/// Uses absolute paths throughout (design divergence from sketch §2).
pub fn link_executable(
    output_path: &Path,
    module_o_paths: &[PathBuf],
    startup_o_path: &Path,
    bundle_lib_path: &Path,
    platform_rlib_paths: &[PathBuf],
) -> Result<(), CranelispError> {
    let config = LinkerConfig::for_host()?;

    // Extract bundle directory and library name
    let bundle_dir = bundle_lib_path
        .parent()
        .unwrap_or_else(|| Path::new("."));
    let bundle_stem = bundle_lib_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("cranelisp_exe_bundle");
    let lib_name = bundle_stem.strip_prefix("lib").unwrap_or(bundle_stem);

    // Log a condensed summary (shared across drivers).
    log_link_summary(
        output_path,
        startup_o_path,
        module_o_paths,
        lib_name,
        platform_rlib_paths,
    );

    match config.driver {
        LinkDriver::AppleLd => link_executable_apple_ld(
            &config,
            output_path,
            module_o_paths,
            startup_o_path,
            bundle_dir,
            lib_name,
            platform_rlib_paths,
        ),
        LinkDriver::Cc => link_executable_cc(
            output_path,
            module_o_paths,
            startup_o_path,
            bundle_dir,
            lib_name,
            platform_rlib_paths,
        ),
    }
}

/// macOS aarch64: assemble Apple `ld` (ld64) args and invoke bare `ld`
/// (design §11.4, macOS column — unchanged from the pre-§11 path).
#[allow(clippy::too_many_arguments)]
fn link_executable_apple_ld(
    config: &LinkerConfig,
    output_path: &Path,
    module_o_paths: &[PathBuf],
    startup_o_path: &Path,
    bundle_dir: &Path,
    lib_name: &str,
    platform_rlib_paths: &[PathBuf],
) -> Result<(), CranelispError> {
    let sysroot = get_sdk_sysroot()?;
    let arch = config.arch.ok_or_else(|| CranelispError::CodegenError {
        message: "internal: macOS LinkerConfig missing arch".to_string(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })?;
    let (platform, min_version, sdk_version) =
        config.platform_triplet.ok_or_else(|| CranelispError::CodegenError {
            message: "internal: macOS LinkerConfig missing platform triplet".to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    let mut ld_args: Vec<String> = vec![
        "-arch".to_string(),
        arch.to_string(),
        "-dead_strip".to_string(),
        "-o".to_string(),
        output_path.to_string_lossy().to_string(),
        "-e".to_string(),
        // The Mach-O linker prepends `_` to the entry symbol name.
        format!("_{}", config.stub_entry_symbol),
    ];

    // Startup stub first
    ld_args.push(startup_o_path.to_string_lossy().to_string());

    // Module .o files
    for o_path in module_o_paths {
        ld_args.push(o_path.to_string_lossy().to_string());
    }

    // Runtime bundle library
    ld_args.push(format!("-L{}", bundle_dir.to_string_lossy()));
    ld_args.push(format!("-l{lib_name}"));

    // Platform rlibs (force-loaded for #[export_name] symbols)
    for rlib_path in platform_rlib_paths {
        ld_args.push("-force_load".to_string());
        ld_args.push(rlib_path.to_string_lossy().to_string());
    }

    // Platform version (required by modern ld)
    ld_args.push("-platform_version".to_string());
    ld_args.push(platform.to_string());
    ld_args.push(min_version.to_string());
    ld_args.push(sdk_version.to_string());

    // System library and SDK root
    ld_args.push("-lSystem".to_string());
    ld_args.push("-syslibroot".to_string());
    ld_args.push(sysroot);

    run_linker("ld", &ld_args)
}

/// Linux aarch64: drive `cc` (gcc) so the crt objects, dynamic-linker path,
/// default search paths, and libc are supplied by the driver (design §11.4).
///
/// No `-e` (crt's `_start` is the default entry; our `main` is the C entry),
/// no `-syslibroot`, no `-platform_version`. `--whole-archive` wraps the
/// platform objects (the GNU equivalent of macOS `-force_load`); for Phase 1
/// the rlib list is normally empty.
fn link_executable_cc(
    output_path: &Path,
    module_o_paths: &[PathBuf],
    startup_o_path: &Path,
    bundle_dir: &Path,
    lib_name: &str,
    platform_rlib_paths: &[PathBuf],
) -> Result<(), CranelispError> {
    let mut cc_args: Vec<String> = vec![
        "-o".to_string(),
        output_path.to_string_lossy().to_string(),
    ];

    // Startup stub (the C `main`) first.
    cc_args.push(startup_o_path.to_string_lossy().to_string());

    // Module .o files (includes the user-main alias .o, appended by the caller).
    for o_path in module_o_paths {
        cc_args.push(o_path.to_string_lossy().to_string());
    }

    // Platform statics — GNU `--whole-archive` is the equivalent of macOS
    // `-force_load`, pulling in the platform's `#[export_name]` GOT/manifest/
    // layout-hash symbols. Normally empty for Phase 1 (non-platform programs).
    //
    // 0324 Phase 2 (design §11.5, option 1): a real Rust `.rlib` is an `ar`
    // archive carrying a `lib.rmeta` (+ `lib.rmeta-link`) metadata member that
    // GNU `ld`/mold reject under `--whole-archive` ("file format not
    // recognized"). So instead of whole-archiving the raw `.rlib`, we extract
    // its object members (the `*.rcgu.o`s — skipping the rmeta family) into a
    // deterministic per-platform cache dir and whole-archive only those `.o`s.
    //
    // ORDER: the whole-archive platform objects MUST precede the runtime bundle
    // `-l`. A platform object references `cranelisp_platform::adt::*` (and other
    // workspace symbols) that live in the bundle; GNU `ld` resolves a static
    // archive (`.a`) only against symbols left-undefined by inputs seen SO FAR.
    // If the bundle came first, the later platform objects' fresh undefined refs
    // (`set_global_schema`, …) would never be satisfied. Placed before the
    // bundle, the platform's undefined refs are open when the bundle is scanned.
    if !platform_rlib_paths.is_empty() {
        // The startup `.o` lives in the cache dir (session_v4.rs writes both
        // there); use its parent as the stable extraction-root so the
        // extracted `.o`s sit beside the other link inputs and are debuggable.
        let cache_dir = startup_o_path.parent().unwrap_or_else(|| Path::new("."));
        cc_args.push("-Wl,--whole-archive".to_string());
        for rlib_path in platform_rlib_paths {
            let objects = extract_rlib_objects(rlib_path, cache_dir)?;
            for obj in objects {
                cc_args.push(obj.to_string_lossy().to_string());
            }
        }
        cc_args.push("-Wl,--no-whole-archive".to_string());
    }

    // Runtime bundle library (embeds Rust std + the workspace platform crate).
    cc_args.push(format!("-L{}", bundle_dir.to_string_lossy()));
    cc_args.push(format!("-l{lib_name}"));

    // Rust-std external deps that must be satisfied at final link. The driver
    // supplies `-lc`/`-lgcc_s`; std additionally needs these (confirmed
    // empirically during implementation — see design §11.4).
    cc_args.push("-lpthread".to_string());
    cc_args.push("-ldl".to_string());
    cc_args.push("-lm".to_string());

    run_linker("cc", &cc_args)
}

/// Extract the object members of a Rust `.rlib` so they can be whole-archived
/// individually on Linux (0324 Phase 2 / design §11.5, option 1).
///
/// A Rust `.rlib` is a GNU `ar` archive of object members (`*.rcgu.o`) PLUS a
/// `lib.rmeta` metadata member (and a `lib.rmeta-link` sidecar). GNU `ld`/mold
/// under `--whole-archive` try to link EVERY member as an object and choke on
/// the rmeta members ("file format not recognized") — Apple `ld64` tolerates
/// this, GNU does not. So we list the archive (`ar t`), keep only the object
/// members (names ending in `.o`, which excludes `lib.rmeta` /
/// `lib.rmeta-link`), and extract just those into a deterministic per-rlib dir
/// under the cache (`<cache>/__plat_<stem>/`), returning the extracted `.o`
/// paths for the caller to whole-archive.
///
/// The extraction dir is deterministic (not a random temp) so paths stay stable
/// across builds and are inspectable when a link fails. Shells out to the
/// system `ar` (already required on the Linux toolchain) rather than adding an
/// `ar`/`object` crate dependency — neither is a dependency of this crate.
fn extract_rlib_objects(
    rlib_path: &Path,
    cache_dir: &Path,
) -> Result<Vec<PathBuf>, CranelispError> {
    let stem = rlib_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("platform");
    let out_dir = cache_dir.join(format!("__plat_{stem}"));

    // Fresh extraction each link: clear any stale objects so a rebuilt rlib
    // does not leave orphaned members behind in the deterministic dir.
    if out_dir.exists() {
        std::fs::remove_dir_all(&out_dir).map_err(|e| CranelispError::CodegenError {
            message: format!(
                "failed to clear platform-object dir {}: {e}",
                out_dir.display()
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    }
    std::fs::create_dir_all(&out_dir).map_err(|e| CranelispError::CodegenError {
        message: format!(
            "failed to create platform-object dir {}: {e}",
            out_dir.display()
        ),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })?;

    // List the archive members. `ar t` prints one member name per line.
    let listing = Command::new("ar")
        .arg("t")
        .arg(rlib_path)
        .output()
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to run `ar t {}`: {e}", rlib_path.display()),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    if !listing.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "`ar t {}` failed:\n{}",
                rlib_path.display(),
                String::from_utf8_lossy(&listing.stderr)
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    // Keep only object members. Rust rlib objects end in `.o` (the `*.rcgu.o`
    // codegen units); `lib.rmeta` / `lib.rmeta-link` do not end in `.o` and are
    // dropped — they are the members GNU `--whole-archive` rejects.
    let object_members: Vec<String> = String::from_utf8_lossy(&listing.stdout)
        .lines()
        .map(str::trim)
        .filter(|m| !m.is_empty() && m.ends_with(".o"))
        .map(str::to_string)
        .collect();

    if object_members.is_empty() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "platform rlib {} contains no object members to whole-archive",
                rlib_path.display()
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    // Extract just the object members into the per-rlib dir. GNU `ar` supports
    // `--output=DIR` to place extracted members somewhere other than cwd.
    let extract = Command::new("ar")
        .arg(format!("--output={}", out_dir.display()))
        .arg("x")
        .arg(rlib_path)
        .args(&object_members)
        .output()
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to run `ar x {}`: {e}", rlib_path.display()),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    if !extract.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "`ar x {}` failed:\n{}",
                rlib_path.display(),
                String::from_utf8_lossy(&extract.stderr)
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    Ok(object_members
        .into_iter()
        .map(|m| out_dir.join(m))
        .collect())
}

/// Spawn the linker driver and surface a non-zero exit as a `CodegenError`.
fn run_linker(program: &str, args: &[String]) -> Result<(), CranelispError> {
    let output = Command::new(program)
        .args(args)
        .output()
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to run {program}: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    if !output.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "linker ({program}) failed:\n{}",
                String::from_utf8_lossy(&output.stderr)
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    Ok(())
}

/// Get the macOS SDK sysroot path via `xcrun --show-sdk-path`.
fn get_sdk_sysroot() -> Result<String, CranelispError> {
    let output = Command::new("xcrun")
        .args(["--show-sdk-path"])
        .output()
        .map_err(|e| CranelispError::CodegenError {
            message: format!(
                "failed to run xcrun: {e} (is Xcode Command Line Tools installed?)"
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    if !output.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "xcrun --show-sdk-path failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

/// Log a condensed linking summary to stderr.
fn log_link_summary(
    output_path: &Path,
    startup_o: &Path,
    module_o_paths: &[PathBuf],
    lib_name: &str,
    platform_rlib_paths: &[PathBuf],
) {
    let mut o_names: Vec<String> = Vec::new();

    o_names.push(
        startup_o
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string(),
    );
    for o_path in module_o_paths {
        o_names.push(
            o_path
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string(),
        );
    }

    let mut lib_parts: Vec<String> = vec![format!("-l{lib_name}")];
    for rlib_path in platform_rlib_paths {
        lib_parts.push(format!(
            "-force_load {}",
            rlib_path
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
        ));
    }

    eprintln!(
        "; Linking: {} {} -o {}",
        o_names.join(" "),
        lib_parts.join(" "),
        output_path.to_string_lossy()
    );
}

// ── Platform rlib locator ───────────────────────────────────────────────

/// Find the static `.rlib` for each linked platform (platform-interface.md §1).
///
/// A `--link` of a platform-using program statically links the platform's rlib
/// (`-force_load`ed by [`link_executable`]) so the platform's `#[export_name]`
/// GOT + manifest + layout-hash symbols (`__cranelisp_got_platform_<name>`,
/// `cranelisp_platform_manifest`, `__cranelisp_layout_hash_<name>`) resolve as
/// ordinary linker symbols in the produced binary — no `dlopen` exists in a
/// linked program (§1, §7.3).
///
/// The cdylib the live session `dlopen`ed and the rlib `--link` needs are sibling
/// artifacts the platform crate builds together (`crate-type = ["cdylib",
/// "rlib"]`); only the rlib carries the archive members `-force_load` needs. We
/// re-resolve the rlib by platform name against the same search roots
/// [`crate::platform::resolve_platform_path`] uses for the dylib, swapping the
/// extension to `rlib` and the Cargo `libcranelisp_<name>` naming (rlibs are
/// always lib-prefixed).
///
/// A platform whose rlib cannot be located is an error: the program declared
/// `(platform "<name>")`, so the standalone binary cannot run without it.
pub fn find_platform_rlibs(
    platform_names: &[String],
    project_root: &Path,
    lib_dirs: &[PathBuf],
    platform_dirs: &[PathBuf],
) -> Result<Vec<PathBuf>, CranelispError> {
    let mut rlibs = Vec::with_capacity(platform_names.len());
    for name in platform_names {
        let rlib = resolve_platform_rlib(name, project_root, lib_dirs, platform_dirs)
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!(
                    "platform '{name}' was loaded at compile time but its static \
                     rlib (lib{}.rlib) could not be found for --link; build the \
                     platform crate (it must produce both a cdylib and an rlib) \
                     or place the rlib on the platform search path",
                    format!("cranelisp_{}", name.replace('-', "_")),
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        rlibs.push(rlib);
    }
    Ok(rlibs)
}

/// Resolve a single platform's static `.rlib` against the dylib search roots.
///
/// Mirrors [`crate::platform::resolve_platform_path`] (project tree → lib dirs →
/// platform dirs) but for the `lib{crate_name}.rlib` artifact. The bare
/// `{name}.rlib` form is also tried for an explicitly-placed rlib.
fn resolve_platform_rlib(
    name: &str,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    platform_dirs: &[PathBuf],
) -> Option<PathBuf> {
    let crate_name = format!("cranelisp_{}", name.replace('-', "_"));

    let check_dir = |dir: &Path| -> Option<PathBuf> {
        let cargo_candidate = dir.join(format!("lib{crate_name}.rlib"));
        if cargo_candidate.is_file() {
            return Some(cargo_candidate);
        }
        let plain = dir.join(format!("{name}.rlib"));
        if plain.is_file() {
            return Some(plain);
        }
        None
    };

    // Tier 1: {project_root}/platforms/
    if let Some(path) = check_dir(&project_root.join("platforms")) {
        return Some(path);
    }
    // Tier 2: {lib_dir}/platforms/
    for lib_dir in lib_dirs {
        if let Some(path) = check_dir(&lib_dir.join("platforms")) {
            return Some(path);
        }
    }
    // Tier 3: extra platform dirs (includes target/debug, target/release).
    for dir in platform_dirs {
        if let Some(path) = check_dir(dir) {
            return Some(path);
        }
    }
    None
}

// ── Bundle library locator ──────────────────────────────────────────────

/// Find the `libcranelisp_exe_bundle.a` static library.
///
/// Search order:
/// 1. `CRANELISP_BUNDLE_PATH` environment variable
/// 2. Same directory as the `cranelisp` binary
/// 3. Sibling directories under `target/` (debug/release)
pub fn find_bundle_lib() -> Result<PathBuf, CranelispError> {
    // Try env var first
    if let Ok(path) = std::env::var("CRANELISP_BUNDLE_PATH") {
        let p = PathBuf::from(path);
        if p.exists() {
            return Ok(p);
        }
    }

    // Try relative to the current executable
    if let Ok(exe_path) = std::env::current_exe()
        && let Some(exe_dir) = exe_path.parent()
    {
        let candidate = exe_dir.join("libcranelisp_exe_bundle.a");
        if candidate.exists() {
            return Ok(candidate);
        }

        // Try sibling directories under target/
        if let Some(target_dir) = exe_dir.parent() {
            for profile in &["debug", "release"] {
                let candidate =
                    target_dir.join(profile).join("libcranelisp_exe_bundle.a");
                if candidate.exists() {
                    return Ok(candidate);
                }
            }
        }
    }

    Err(CranelispError::CodegenError {
        message: "could not find libcranelisp_exe_bundle.a — \
                  build it with `cargo build -p cranelisp-exe-bundle` or \
                  set CRANELISP_BUNDLE_PATH"
            .to_string(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })
}

// ── Platform manifest name collection ───────────────────────────────────

/// The C-ABI symbol every platform DLL/rlib exports for its manifest entry
/// point (`declare_platform!` emits it `#[unsafe(no_mangle)]`, so it is the same
/// link name for every platform — `cranelisp-platform/src/lib.rs`).
///
/// Calling it populates that platform's exported GOT (manifest order IS GOT slot
/// order) and returns the descriptor block. The startup stub declares it as an
/// imported zero-arg fn and passes its address to `cranelisp_init_platform`
/// (`generate_startup_object`).
const PLATFORM_MANIFEST_SYMBOL: &str = "cranelisp_platform_manifest";

/// Collect the platform manifest symbol names the startup stub must call
/// (one per linked platform, to force each platform's GOT-population code in).
///
/// Sourced from the loaded-platform registry (`SharedState::kept_dlls`) by the
/// caller, which passes the platform count.
///
/// **Single-platform `--link` is fully supported.** Because `declare_platform!`
/// exports the manifest entry point `#[unsafe(no_mangle)]`, every platform
/// shares the link name `cranelisp_platform_manifest`; `-force_load`ing two
/// platform rlibs would collide on that symbol (and on `__cranelisp_init_*`
/// helpers). Multi-platform `--link` therefore needs per-platform mangled
/// manifest names — out of scope for S79 (no program links more than one
/// platform). With one linked platform the shared name resolves unambiguously.
pub fn collect_platform_manifest_names(platform_count: usize) -> Vec<String> {
    // One manifest call per linked platform (each populates its own GOT). With
    // the shared no_mangle symbol this is correct for the single-platform case;
    // see the doc comment for the multi-platform limitation.
    vec![PLATFORM_MANIFEST_SYMBOL.to_string(); platform_count]
}

// ── Tests ───────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{DefKind, Scheme, Symbol, TypeName, Visibility};
    use std::collections::HashMap;

    fn make_main_entry(ty: Type) -> ModuleEntry<crate::code::Code> {
        ModuleEntry::def(
            Scheme { type_vars: vec![], constraints: HashMap::new(), ty },
            DefKind::UserFn { constrained_fn: None },
        )
        .visibility(Visibility::Public)
        .build()
    }

    // spec: design/backend/executable-generation.md §7 — main :: () -> Int accepted
    #[test]
    fn validate_main_returns_int() {
        let mut st = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        st.insert(
            Symbol::from("main"),
            make_main_entry(Type::Fn(vec![], Box::new(Type::Int))),
        );
        let result = validate_main(&st).unwrap();
        assert_eq!(result, MainReturnKind::Int);
    }

    // spec: design/backend/executable-generation.md §7 — main :: () -> IO _ accepted
    #[test]
    fn validate_main_returns_io() {
        let mut st = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        st.insert(
            Symbol::from("main"),
            make_main_entry(Type::Fn(
                vec![],
                Box::new(Type::ADT(cranelisp_types::FQTypeName::new(
                    ModuleFullPath::from("primitives"),
                    TypeName::from("IO"),
                ), vec![Type::Int])),
            )),
        );
        let result = validate_main(&st).unwrap();
        assert_eq!(result, MainReturnKind::Io);
    }

    // spec: design/backend/executable-generation.md §7 — missing main is error
    #[test]
    fn validate_main_missing() {
        let st = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        let err = validate_main(&st).unwrap_err();
        match err {
            CranelispError::CodegenError { message, .. } => {
                assert!(message.contains("no 'main' function"));
            }
            _ => panic!("expected CodegenError"),
        }
    }

    // spec: design/backend/executable-generation.md §7 — main :: () -> String is error
    #[test]
    fn validate_main_wrong_return_type() {
        let mut st = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        st.insert(
            Symbol::from("main"),
            make_main_entry(Type::Fn(vec![], Box::new(Type::String))),
        );
        let err = validate_main(&st).unwrap_err();
        match err {
            CranelispError::CodegenError { message, .. } => {
                assert!(message.contains("main must return Int or IO"));
            }
            _ => panic!("expected CodegenError"),
        }
    }

    // spec: design/backend/executable-generation.md §7 — main with params is error
    #[test]
    fn validate_main_with_params() {
        let mut st = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        st.insert(
            Symbol::from("main"),
            make_main_entry(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
        );
        let err = validate_main(&st).unwrap_err();
        match err {
            CranelispError::CodegenError { message, .. } => {
                assert!(message.contains("zero-argument"));
            }
            _ => panic!("expected CodegenError"),
        }
    }

    // spec: design/backend/executable-generation.md §6 — bundle lib not found produces clear error
    #[test]
    fn find_bundle_lib_not_found() {
        unsafe { std::env::remove_var("CRANELISP_BUNDLE_PATH") };
        // May or may not find the lib depending on build state.
        if let Err(e) = find_bundle_lib() {
            match e {
                CranelispError::CodegenError { message, .. } => {
                    assert!(message.contains("libcranelisp_exe_bundle.a"));
                    assert!(message.contains("cargo build -p cranelisp-exe-bundle"));
                }
                _ => panic!("expected CodegenError"),
            }
        }
    }

    // spec: design/backend/executable-generation.md §6 — bundle lib found via env var
    #[test]
    fn find_bundle_lib_via_env() {
        let dir = tempfile::tempdir().unwrap();
        let bundle_path = dir.path().join("libcranelisp_exe_bundle.a");
        std::fs::write(&bundle_path, b"fake bundle").unwrap();
        unsafe { std::env::set_var("CRANELISP_BUNDLE_PATH", &bundle_path) };
        let result = find_bundle_lib().unwrap();
        assert_eq!(result, bundle_path);
        unsafe { std::env::remove_var("CRANELISP_BUNDLE_PATH") };
    }

    // spec: platform-interface.md §7.3 — no linked platforms ⇒ no rlibs.
    #[test]
    fn find_platform_rlibs_empty_when_no_platforms() {
        let dir = tempfile::tempdir().unwrap();
        let rlibs = find_platform_rlibs(&[], dir.path(), &[], &[]).unwrap();
        assert!(rlibs.is_empty());
    }

    // spec: platform-interface.md §7.3 — a declared platform whose rlib is
    // absent is a hard --link error (the standalone binary needs the static
    // platform code).
    #[test]
    fn find_platform_rlibs_missing_is_error() {
        let dir = tempfile::tempdir().unwrap();
        let err = find_platform_rlibs(
            &["shapes".to_string()],
            dir.path(),
            &[],
            &[],
        )
        .unwrap_err();
        match err {
            CranelispError::CodegenError { message, .. } => {
                assert!(message.contains("shapes"));
                assert!(message.contains("rlib"));
            }
            _ => panic!("expected CodegenError"),
        }
    }

    // spec: platform-interface.md §7.3 — the rlib resolves against the platform
    // search roots (tier 3) under the Cargo `libcranelisp_<name>.rlib` name.
    #[test]
    fn find_platform_rlibs_resolves_cargo_rlib() {
        let dir = tempfile::tempdir().unwrap();
        let target = dir.path().join("target-debug");
        std::fs::create_dir_all(&target).unwrap();
        let rlib = target.join("libcranelisp_shapes.rlib");
        std::fs::write(&rlib, b"fake rlib").unwrap();

        let rlibs = find_platform_rlibs(
            &["shapes".to_string()],
            dir.path(),
            &[],
            &[target],
        )
        .unwrap();
        assert_eq!(rlibs, vec![rlib]);
    }

    // spec: platform-interface.md §7.3 — manifest symbol per linked platform;
    // none linked ⇒ none collected.
    #[test]
    fn collect_platform_manifest_names_counts() {
        assert!(collect_platform_manifest_names(0).is_empty());
        assert_eq!(
            collect_platform_manifest_names(1),
            vec!["cranelisp_platform_manifest".to_string()]
        );
    }

    // spec: design/backend/executable-generation.md §11.6 — host-dispatched
    // LinkerConfig: macOS → AppleLd / start / main; Linux → Cc / main /
    // cranelisp_user_main.
    #[test]
    fn linker_config_for_host() {
        if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            let config = LinkerConfig::for_host().unwrap();
            assert_eq!(config.driver, LinkDriver::AppleLd);
            assert_eq!(config.arch, Some("arm64"));
            assert_eq!(config.stub_entry_symbol, "start");
            assert_eq!(config.user_main_symbol, "main");
            assert_eq!(config.platform_triplet, Some(("macos", "14.0", "14.0")));
        } else if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
            let config = LinkerConfig::for_host().unwrap();
            assert_eq!(config.driver, LinkDriver::Cc);
            assert_eq!(config.stub_entry_symbol, "main");
            assert_eq!(config.user_main_symbol, "cranelisp_user_main");
            assert_eq!(config.arch, None);
            assert_eq!(config.platform_triplet, None);
        }
    }

    // spec: design/backend/executable-generation.md §11.5 — Phase 2 rlib object
    // extraction: only object members (`*.o`) are extracted; the rmeta family
    // (`lib.rmeta` / `lib.rmeta-link`) is skipped, and the extracted `.o`s land
    // in a deterministic `__plat_<stem>/` dir under the supplied cache dir.
    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn extract_rlib_objects_keeps_only_objects() {
        // Build a tiny `ar` archive with one object-like member and one
        // rmeta-like member, then assert only the `.o` is extracted. Uses the
        // system `ar` (same tool the extractor shells out to).
        let dir = tempfile::tempdir().unwrap();
        let obj = dir.path().join("unit.o");
        std::fs::write(&obj, b"\x7fELF-not-really-but-ends-in-o").unwrap();
        let rmeta = dir.path().join("lib.rmeta");
        std::fs::write(&rmeta, b"rust-metadata").unwrap();
        let rlib = dir.path().join("libfake_platform.rlib");
        let status = std::process::Command::new("ar")
            .arg("rcs")
            .arg(&rlib)
            .arg(&obj)
            .arg(&rmeta)
            .status()
            .unwrap();
        assert!(status.success(), "ar rcs failed to build fixture archive");

        let cache = dir.path().join("cache");
        std::fs::create_dir_all(&cache).unwrap();
        let objects = extract_rlib_objects(&rlib, &cache).unwrap();

        // Exactly one object member, the `.o`; the rmeta member is excluded.
        assert_eq!(objects.len(), 1, "extracted: {objects:?}");
        let extracted = &objects[0];
        assert_eq!(extracted.file_name().unwrap(), "unit.o");
        assert!(extracted.exists(), "extracted .o must be on disk");
        // Deterministic dir derived from the rlib stem.
        assert!(extracted.starts_with(cache.join("__plat_libfake_platform")));
        // The rmeta member was NOT extracted.
        assert!(!cache.join("__plat_libfake_platform").join("lib.rmeta").exists());
    }

    // spec: design/backend/executable-generation.md §11.3 — host_entry_symbols
    // returns the (stub_entry, user_main) pair the call site threads into the
    // stub + alias generators.
    #[test]
    fn host_entry_symbols_match_config() {
        if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            assert_eq!(host_entry_symbols().unwrap(), ("start", "main"));
        } else if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
            assert_eq!(
                host_entry_symbols().unwrap(),
                ("main", "cranelisp_user_main")
            );
        }
    }
}
