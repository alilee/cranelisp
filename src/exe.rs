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
/// * `main_returns_io` — passed to `cranelisp_run_program` as the flag that
///   decides whether the unified driver forces the IO task tree before
///   producing the exit code (FIXME 0366 — the stub no longer emits a direct
///   `cranelisp_run_io` call).
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

    // Declare `cranelisp_run_program` as imported — the unified program driver
    // (FIXME 0366). It owns the WHOLE drive-main → pre-IO-drain → IO-trampoline →
    // post-IO-drain sequence that the `--run` host also calls; the stub shrinks
    // to one call + an outcome branch. Signature:
    //   `(main_ptr: i64, main_returns_io: i8) -> ProgramOutcome { i64, i32 }`.
    // The `ProgramOutcome` `#[repr(C)]` carrier (i64 exit_code + i32 error_kind)
    // returns in the AArch64 AAPCS / SysV integer return registers (x0:x1 /
    // rax:rdx), matched here by the two scalar return AbiParams. `main_returns_io`
    // is passed as an i8 bool (the C-ABI `bool` width).
    let mut run_program_sig = obj_module.make_signature();
    run_program_sig.params.push(AbiParam::new(types::I64)); // main_ptr
    run_program_sig.params.push(AbiParam::new(types::I8)); // main_returns_io (bool)
    run_program_sig.returns.push(AbiParam::new(types::I64)); // exit_code
    run_program_sig.returns.push(AbiParam::new(types::I32)); // error_kind
    let run_program_func_id = obj_module
        .declare_function("cranelisp_run_program", Linkage::Import, &run_program_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare cranelisp_run_program: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    // Declare `cranelisp_check_runtime_error` as imported (zero-arg). Since the
    // FIXME 0366 unification the stub calls this at ONE site — on a non-zero
    // `ProgramOutcome::error_kind` after `cranelisp_run_program`. The driver
    // left the relevant slot SET; this gate drains it, prints the message to
    // stderr, and `exit(1)`s — a clean batch-mode exit mirroring the `--run`
    // host (spec §12.7.4.2). It drains BOTH the runtime-error and dispatch-fault
    // slots, so it surfaces the pre-IO (FIXME 0399) and during-IO (FIXME 0401)
    // cases with one body. Resolved by the system linker against
    // `cranelisp-intrinsics` (force-linked via `cranelisp-exe-bundle`'s
    // `pub use …::panic`).
    let check_runtime_error_sig = obj_module.make_signature();
    let check_runtime_error_func_id = obj_module
        .declare_function(
            "cranelisp_check_runtime_error",
            Linkage::Import,
            &check_runtime_error_sig,
        )
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare cranelisp_check_runtime_error: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

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

        // 2. Run the program via the unified driver (FIXME 0366). Take main's
        // address (it is imported `Linkage::Import` and never called directly
        // now) + the `main_returns_io` flag, and hand the whole
        // drive-main → drain → trampoline → drain sequence to
        // `cranelisp_run_program`. It returns `ProgramOutcome { exit_code,
        // error_kind }` in the two integer return registers.
        let main_ref = obj_module.declare_func_in_func(main_func_id, builder.func);
        let main_addr = builder.ins().func_addr(types::I64, main_ref);
        let returns_io_flag = builder
            .ins()
            .iconst(types::I8, if main_returns_io { 1 } else { 0 });
        let run_program_ref =
            obj_module.declare_func_in_func(run_program_func_id, builder.func);
        let run_inst = builder
            .ins()
            .call(run_program_ref, &[main_addr, returns_io_flag]);
        let results = builder.inst_results(run_inst);
        let exit_code_i64 = results[0];
        let error_kind = results[1];

        // 3. Outcome branch: on a non-zero `error_kind` the driver left the
        // relevant slot SET — drain+print+exit(1) via `cranelisp_check_runtime_error`
        // (it prints from whichever slot is set and exits). Otherwise exit with
        // the reduced exit_code. This is the stub's whole error-surfacing
        // responsibility (the three former lockstep slot-check points now live
        // once inside `cranelisp_run_program`).
        let error_block = builder.create_block();
        let clean_block = builder.create_block();
        let zero = builder.ins().iconst(types::I32, 0);
        let is_error = builder
            .ins()
            .icmp(IntCC::NotEqual, error_kind, zero);
        builder.ins().brif(is_error, error_block, &[], clean_block, &[]);

        // Error path: drain the SET slot, print, and exit(1) inside the export.
        builder.switch_to_block(error_block);
        builder.seal_block(error_block);
        let check_re_ref =
            obj_module.declare_func_in_func(check_runtime_error_func_id, builder.func);
        builder.ins().call(check_re_ref, &[]);
        // `cranelisp_check_runtime_error` exits on a set slot; defensively trap
        // if control returns (it won't on a genuine error_kind != 0).
        builder.ins().trap(TrapCode::user(1).unwrap());

        // Clean path: exit(exit_code).
        builder.switch_to_block(clean_block);
        builder.seal_block(clean_block);
        let exit_code = builder.ins().ireduce(types::I32, exit_code_i64);
        let exit_ref = obj_module.declare_func_in_func(exit_func_id, builder.func);
        builder.ins().call(exit_ref, &[exit_code]);
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

/// Validate that the entry module exports a `main` function with the required
/// batch-mode signature `(Fn [] (IO _))` (spec §10.6 / §12.6 / §2.1 / §8.11).
///
/// A batch `main` MUST return `IO _`: a non-IO `main` that drives the program's
/// effects is a category error against the §10.1.2 purity invariant — a pure
/// (`Int`/`Bool`/…) result could be memoized, reordered, or elided while the
/// host performs effects. The exit code is the *inner* `Int` of the resulting
/// `IO Int` (§10.6.1) — a bare-`Int` main would need special-casing. The REPL
/// is exempt (§10.6.2 — no `main` requirement), so this seam (reached only by
/// the two batch entry modes) is the correct enforcement point, NOT typecheck.
///
/// Returns `Ok(())` for an acceptable `(Fn [] (IO _))` main; a spec-grounded
/// error naming the required `(Fn [] (IO _))` shape otherwise.
pub fn validate_main(entry_symbols: &crate::code::SessionSymbolTable) -> Result<(), CranelispError> {
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

/// Enforce that `main`'s type is `(Fn [] (IO _))`.
///
/// Only the `IO` ADT return satisfies the gate; a bare `Int`/`Bool`/… return is
/// rejected (no lenient "or Int" acceptance — spec §10.6 / §12.6, ruling
/// SPRINT.md 0317 fork). A non-zero-arity main is also rejected.
fn classify_main_return_type(ty: &Type) -> Result<(), CranelispError> {
    match ty {
        Type::Fn(params, ret) if params.is_empty() => match ret.as_ref() {
            Type::ADT(name, _) if name.name.as_ref() == "IO" => Ok(()),
            other => Err(CranelispError::CodegenError {
                message: format!(
                    "main must return `IO _` (required shape `(Fn [] (IO _))`), found: {}",
                    type_display_brief(other)
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }),
        },
        _ => Err(CranelispError::CodegenError {
            message: format!(
                "main must be a zero-argument function returning `IO _` \
                 (required shape `(Fn [] (IO _))`), found: {}",
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
    // The callable slot now rides on the `DefKind` variant (S83 reshape,
    // FIXME 0356/0357) — read it through the `callable_got_slot()` chokepoint.
    // `main` is a concrete user fn, so a pinned slot is expected.
    match entry {
        ModuleEntry::Def { .. } => entry.callable_got_slot().ok_or_else(|| {
            CranelispError::CodegenError {
                message: "entry module's 'main' has no GOT slot — typecheck did \
                          not pin a slot index"
                    .to_string(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        }),
        _ => Err(CranelispError::CodegenError {
            message: "entry module's 'main' is not a Def entry".to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

// ── Link executable ─────────────────────────────────────────────────────

/// The startup-stub export symbol and the user-main alias symbol for the host
/// (design §11.3). Re-exported from the `link` module so `session_v4.rs` keeps
/// its `crate::exe::host_entry_symbols()` call site.
pub(crate) use crate::link::host_entry_symbols;

/// Link module `.o` files and startup `.o` with the runtime bundle and platform
/// rlibs into a native executable.
///
/// Composes a platform-neutral [`crate::link::LinkRequest`] from its params and
/// hands it to the host's [`crate::link::Linker`] (S80 Wave 2E). No platform
/// link token (`-force_load`, `--whole-archive`, `-arch`, …) appears here — they
/// are rendered solely inside the chosen driver impl, which also produces the
/// `; Linking: …` diagnostic from the same arg-building path (the D4 fix). Uses
/// absolute paths throughout (design divergence from sketch §2).
pub fn link_executable(
    output_path: &Path,
    module_o_paths: &[PathBuf],
    startup_o_path: &Path,
    bundle_lib_path: &Path,
    platform_rlib_paths: &[PathBuf],
) -> Result<(), CranelispError> {
    // Extract bundle directory and library name (the `lib`-stripped stem).
    let bundle_dir = bundle_lib_path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();
    let bundle_stem = bundle_lib_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("cranelisp_exe_bundle");
    let lib_name = bundle_stem.strip_prefix("lib").unwrap_or(bundle_stem);

    // `entry_symbol` is the host's stub-entry symbol — the same name the stub
    // actually exported (`host_entry_symbols().0`), so the linker references it.
    let (stub_entry_symbol, _user_main_symbol) = crate::link::host_entry_symbols()?;

    let req = crate::link::LinkRequest {
        startup_obj: startup_o_path.to_path_buf(),
        module_objs: module_o_paths.to_vec(),
        bundle_lib: crate::link::BundleLib {
            dir: bundle_dir,
            name: lib_name.to_string(),
        },
        force_include: platform_rlib_paths
            .iter()
            .map(|rlib| crate::link::ForceIncludeArchive { rlib: rlib.clone() })
            .collect(),
        entry_symbol: stub_entry_symbol.to_string(),
        dead_strip: true,
        output: output_path.to_path_buf(),
    };

    let linker = crate::link::for_host()?;
    // The diagnostic is rendered by the SAME driver that executes the link,
    // from its own `build_args` — so the printed command cannot drift from the
    // real one (the D4 fix). On Linux it shows GNU tokens; on macOS Apple tokens.
    eprintln!("{}", linker.describe(&req));
    linker.link(&req)
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
            DefKind::UserFn {
                fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0 },
            },
        )
        .visibility(Visibility::Public)
        .build()
    }

    // spec: spec/10-io.md §10.6 / spec/12-runtime.md §12.6 — a bare-`Int` batch
    // main `(Fn [] Int)` is REJECTED (no lenient "or Int" acceptance; SPRINT.md
    // 0317-fork ruling: `main : (Fn [] (IO _))` stands enforceable).
    #[test]
    fn validate_main_bare_int_return_is_rejected() {
        let mut st = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        st.insert(
            Symbol::from("main"),
            make_main_entry(Type::Fn(vec![], Box::new(Type::Int))),
        );
        let err = validate_main(&st).unwrap_err();
        match err {
            CranelispError::CodegenError { message, .. } => {
                assert!(message.contains("IO"), "names the IO requirement: {message}");
                assert!(
                    message.contains("(Fn [] (IO _))"),
                    "names the required shape: {message}"
                );
            }
            _ => panic!("expected CodegenError"),
        }
    }

    // spec: spec/10-io.md §10.6 / spec/12-runtime.md §12.6 — a bare-`Bool` batch
    // main `(Fn [] Bool)` is REJECTED with the same `(Fn [] (IO _))` diagnostic.
    #[test]
    fn validate_main_bare_bool_return_is_rejected() {
        let mut st = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        st.insert(
            Symbol::from("main"),
            make_main_entry(Type::Fn(vec![], Box::new(Type::Bool))),
        );
        let err = validate_main(&st).unwrap_err();
        match err {
            CranelispError::CodegenError { message, .. } => {
                assert!(message.contains("IO"), "names the IO requirement: {message}");
                assert!(message.contains("(Fn [] (IO _))"), "names the required shape: {message}");
            }
            _ => panic!("expected CodegenError"),
        }
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
        // An `(Fn [] (IO Int))` main is the canonical batch shape — accepted.
        assert!(validate_main(&st).is_ok());
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
                assert!(message.contains("IO"), "names the IO requirement: {message}");
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

    // spec: design/backend/executable-generation.md §12.6 — `for_host()` returns
    // a `Box<dyn Linker>` on the two supported aarch64 hosts (macOS Apple-ld /
    // Linux cc). The driver identity is now the impl type, not an enum field.
    #[test]
    fn link_for_host_resolves_on_supported_hosts() {
        if cfg!(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))) {
            assert!(crate::link::for_host().is_ok());
        }
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
