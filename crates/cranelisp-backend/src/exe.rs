//! Startup-stub generation for standalone executables (`--link` mode).
//!
//! `generate_startup_object` produces a small `.o` defining a `start` symbol
//! that:
//! 1. Initializes platforms (calls `cranelisp_init_platform` for each manifest),
//! 2. Calls the user's `main` function,
//! 3. If `main` returns IO, calls the IO trampoline (`cranelisp_run_io`),
//! 4. Truncates the i64 result to i32 and calls `exit`.
//!
//! This is link-orchestration assist, NOT codegen: it is called by
//! `int::link_by_name` (not by `compile_to_module`). It lives in
//! `cranelisp-backend` because it uses Cranelift APIs directly; the binary
//! crate orchestrates (validates `main`, collects `.o` paths, invokes the
//! system linker). See `design/backend/executable-generation.md` §4.

use cranelift::prelude::*;
use cranelift_module::{default_libcall_names, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

use cranelisp_types::{ErrorLocation, CranelispError, Span};

/// Generate a startup `.o` that defines `start` (exported, referenced by
/// the linker via `-e _start`) which initializes platforms, calls `main()`,
/// optionally runs the IO trampoline, and calls `exit()`.
///
/// # Arguments
/// * `platform_manifest_names` — symbol names for platform manifest functions
///   (e.g., `["cranelisp_platform_manifest"]`). Empty if no platforms.
/// * `main_returns_io` — if true, inserts a `cranelisp_run_io` call to force
///   the IO task tree before extracting the exit code.
///
/// # Returns
/// The raw bytes of a relocatable object file (Mach-O on macOS aarch64).
///
/// # Linker-symbol ABI (preserved here before the S75 W3 `pub(crate)` narrow)
///
/// The emitted `.o` defines one **`Linkage::Export`** symbol — **`start`** (the
/// system-linker entry, referenced via `-e _start`). It declares the entry
/// function `entry_fn_name` (typically `main`, or module-qualified like
/// `hello/main`) as **`Linkage::Import`** and emits a relocation against it,
/// plus `Linkage::Import` relocations against each platform-manifest name in
/// `platform_manifest_names` and (when `main_returns_io`) against the IO
/// trampoline `cranelisp_run_io`. These imports are resolved at system-link
/// time against the user `.o`s and the runtime/platform archives.
///
/// Narrowed to `pub(crate)` per the S75 W3 /arch re-ruling: the `--link`
/// `start`-`.o` assist is link-orchestration the `--link` driver owns (BC
/// invariant 7 — "the `--link` `_main` alias is int's job, not backend's").
/// The body stays in backend as an internal helper; it is not a boundary.
/// int's call sites (`exe.rs:20` re-export + `session_v4.rs:3991`) re-wire S77.
// `allow(dead_code)`: the only non-test caller is int (currently red post-W2/W3;
// re-wires S77). In-crate unit tests below exercise it. The allow clears the
// lib-target dead_code warning the W3 narrow surfaced without deleting the body
// (deletion is a W4 streamline decision).
#[allow(dead_code)]
pub(crate) fn generate_startup_object(
    platform_manifest_names: &[String],
    main_returns_io: bool,
    entry_fn_name: &str,
) -> Result<Vec<u8>, CranelispError> {
    let isa = crate::cache::object::build_isa(true)?;

    let obj_builder =
        ObjectBuilder::new(isa, "cranelisp_startup", default_libcall_names()).map_err(|e| {
            CranelispError::CodegenError {
                message: format!("failed to create ObjectBuilder: {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
    let mut obj_module = ObjectModule::new(obj_builder);

    // Declare entry function as imported (user's main function, returns i64).
    // The name must match what compile_to_module exports — module-qualified
    // for modules not named "user" or "main" (e.g., "hello/main").
    let mut main_sig = obj_module.make_signature();
    main_sig.returns.push(AbiParam::new(types::I64));
    let main_func_id = obj_module
        .declare_function(entry_fn_name, Linkage::Import, &main_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare {}: {e}", entry_fn_name),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    // Declare `cranelisp_run_io` as imported (IO trampoline)
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

    // Declare `exit` as imported (libc, takes i32)
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
    // unless we call it here directly. `LazyLock::force` is idempotent, so the
    // redundant call in the platform path is harmless.
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

    // Declare `cranelisp_init_platform` as imported (if platforms exist)
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

    // Declare each platform manifest function as imported (need symbol for func_addr)
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

    // Define `start` (exported entry point)
    let start_sig = obj_module.make_signature();
    let start_func_id = obj_module
        .declare_function("start", Linkage::Export, &start_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare start: {e}"),
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

        // 1. Initialize platforms before calling main
        if let Some(init_fid) = init_func_id {
            let init_ref = obj_module.declare_func_in_func(init_fid, builder.func);
            for &manifest_fid in &manifest_func_ids {
                let manifest_ref = obj_module.declare_func_in_func(manifest_fid, builder.func);
                let addr = builder.ins().func_addr(types::I64, manifest_ref);
                builder.ins().call(init_ref, &[addr]);
            }
        }

        // 2. Call main()
        let main_ref = obj_module.declare_func_in_func(main_func_id, builder.func);
        let call_inst = builder.ins().call(main_ref, &[]);
        let main_result = builder.inst_results(call_inst)[0];

        // 3. If main returns IO, force the task tree via trampoline
        let ret_val = if let Some(run_io_fid) = run_io_func_id {
            let run_io_ref = obj_module.declare_func_in_func(run_io_fid, builder.func);
            let run_inst = builder.ins().call(run_io_ref, &[main_result]);
            builder.inst_results(run_inst)[0]
        } else {
            main_result
        };

        // 4. Truncate i64 -> i32 for exit code
        let exit_code = builder.ins().ireduce(types::I32, ret_val);

        // 5. Call exit(code)
        let exit_ref = obj_module.declare_func_in_func(exit_func_id, builder.func);
        builder.ins().call(exit_ref, &[exit_code]);

        // Unreachable after exit, but Cranelift needs a block terminator
        builder.ins().trap(TrapCode::user(1).unwrap());

        builder.finalize();
    }

    let mut ctx = cranelift::codegen::Context::for_function(func);
    obj_module
        .define_function(start_func_id, &mut ctx)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define start: {e:?}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    let product = obj_module.finish();
    let bytes = product.emit().map_err(|e| CranelispError::CodegenError {
        message: format!("failed to emit startup object: {e}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })?;

    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: design/backend/executable-generation.md §4 — startup stub generation (no IO)
    #[test]
    fn generate_startup_object_no_io() {
        let bytes = generate_startup_object(&[], false, "main").unwrap();
        assert!(!bytes.is_empty(), "startup .o should not be empty");
    }

    // spec: design/backend/executable-generation.md §4 — startup stub with IO trampoline
    #[test]
    fn generate_startup_object_with_io() {
        let bytes = generate_startup_object(&[], true, "main").unwrap();
        assert!(!bytes.is_empty(), "startup .o should not be empty");
    }

    // spec: design/backend/executable-generation.md §4 — startup stub with platform init
    #[test]
    fn generate_startup_object_with_platform() {
        let manifest_names = vec!["cranelisp_platform_manifest".to_string()];
        let bytes = generate_startup_object(&manifest_names, false, "main").unwrap();
        assert!(!bytes.is_empty(), "startup .o should not be empty");
    }

    // spec: design/backend/executable-generation.md §4 — startup stub with platform + IO
    #[test]
    fn generate_startup_object_with_platform_and_io() {
        let manifest_names = vec!["cranelisp_platform_manifest".to_string()];
        let bytes = generate_startup_object(&manifest_names, true, "main").unwrap();
        assert!(!bytes.is_empty(), "startup .o should not be empty");
    }

    // spec: design/backend/executable-generation.md §4 — startup stub with module-qualified entry
    #[test]
    fn generate_startup_object_qualified_entry() {
        let bytes = generate_startup_object(&[], false, "hello/main").unwrap();
        assert!(!bytes.is_empty(), "startup .o with qualified entry should not be empty");
    }
}
