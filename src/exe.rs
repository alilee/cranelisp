//! Standalone executable generation.
//!
//! Produces a native macOS aarch64 executable by linking cached module `.o` files
//! with a startup stub and the runtime static library.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use cranelift::prelude::*;
use cranelift_module::{default_libcall_names, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::error::CranelispError;
use crate::module::CompiledModule;
use crate::names::ModuleFullPath;

// ── Startup stub ─────────────────────────────────────────────────────────

/// Generate a startup `.o` that defines `_start` which initializes platforms,
/// calls `main()`, and `exit()`.
///
/// The startup stub:
/// 1. For each platform, calls `cranelisp_init_platform(func_addr(manifest_fn))`
/// 2. Calls the user's `main` function (returns i64)
/// 3. Truncates i64 to i32 via `ireduce`
/// 4. Calls libc `exit(i32)`
pub fn generate_startup_object(
    platform_manifest_names: &[String],
) -> Result<Vec<u8>, CranelispError> {
    let mut flag_builder = settings::builder();
    flag_builder
        .set("is_pic", "true")
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set flag: {}", e),
            span: (0, 0),
        })?;
    let isa_builder =
        cranelift_native::builder().map_err(|msg| CranelispError::CodegenError {
            message: format!("host not supported: {}", msg),
            span: (0, 0),
        })?;
    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to build ISA: {}", e),
            span: (0, 0),
        })?;

    let obj_builder =
        ObjectBuilder::new(isa, "cranelisp_startup", default_libcall_names())
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to create ObjectBuilder: {}", e),
                span: (0, 0),
            })?;
    let mut obj_module = ObjectModule::new(obj_builder);

    // Declare `main` as imported (user's main function, returns i64)
    let mut main_sig = obj_module.make_signature();
    main_sig.returns.push(AbiParam::new(types::I64));
    let main_func_id = obj_module
        .declare_function("main", Linkage::Import, &main_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare main: {}", e),
            span: (0, 0),
        })?;

    // Declare `exit` as imported (libc exit, takes i32, doesn't return)
    let mut exit_sig = obj_module.make_signature();
    exit_sig.params.push(AbiParam::new(types::I32));
    let exit_func_id = obj_module
        .declare_function("exit", Linkage::Import, &exit_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare exit: {}", e),
            span: (0, 0),
        })?;

    // Declare `cranelisp_init_platform` as imported (takes i64 manifest fn ptr, returns void)
    let mut init_sig = obj_module.make_signature();
    init_sig.params.push(AbiParam::new(types::I64));
    let init_func_id = if !platform_manifest_names.is_empty() {
        Some(
            obj_module
                .declare_function("cranelisp_init_platform", Linkage::Import, &init_sig)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare cranelisp_init_platform: {}", e),
                    span: (0, 0),
                })?,
        )
    } else {
        None
    };

    // Declare each platform manifest function as imported (need symbol for func_addr)
    // We use a dummy signature — we only need the address, not to call it directly.
    let mut manifest_func_ids = Vec::new();
    for manifest_name in platform_manifest_names {
        let manifest_sig = obj_module.make_signature();
        let fid = obj_module
            .declare_function(manifest_name, Linkage::Import, &manifest_sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare {}: {}", manifest_name, e),
                span: (0, 0),
            })?;
        manifest_func_ids.push(fid);
    }

    // Define `start` (exported entry point)
    let start_sig = obj_module.make_signature();
    let start_func_id = obj_module
        .declare_function("start", Linkage::Export, &start_sig)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to declare start: {}", e),
            span: (0, 0),
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

        // Initialize platforms before calling main
        if let Some(init_fid) = init_func_id {
            let init_ref = obj_module.declare_func_in_func(init_fid, builder.func);
            for &manifest_fid in &manifest_func_ids {
                let manifest_ref =
                    obj_module.declare_func_in_func(manifest_fid, builder.func);
                let addr = builder.ins().func_addr(types::I64, manifest_ref);
                builder.ins().call(init_ref, &[addr]);
            }
        }

        // Call main()
        let main_ref = obj_module.declare_func_in_func(main_func_id, builder.func);
        let call_inst = builder.ins().call(main_ref, &[]);
        let ret_val = builder.inst_results(call_inst)[0];

        // Truncate i64 → i32 for exit code
        let exit_code = builder.ins().ireduce(types::I32, ret_val);

        // Call exit(code)
        let exit_ref = obj_module.declare_func_in_func(exit_func_id, builder.func);
        builder.ins().call(exit_ref, &[exit_code]);

        // Unreachable after exit, but Cranelift needs a terminator
        builder.ins().trap(TrapCode::user(1).unwrap());

        builder.finalize();
    }

    let mut ctx = cranelift::codegen::Context::for_function(func);
    obj_module
        .define_function(start_func_id, &mut ctx)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define start: {:?}", e),
            span: (0, 0),
        })?;

    let product = obj_module.finish();
    let bytes = product.emit().map_err(|e| CranelispError::CodegenError {
        message: format!("failed to emit startup object: {}", e),
        span: (0, 0),
    })?;

    Ok(bytes)
}

// ── Link executable ──────────────────────────────────────────────────────

/// Link module `.o` files and startup `.o` with the runtime bundle
/// and platform rlibs into a native executable.
///
/// Platform rlibs are ar archives containing `.o` files with `#[export_name]`
/// symbols — `ld` can read them directly as archive inputs.
pub fn link_executable(
    output_path: &Path,
    module_o_paths: &[PathBuf],
    startup_o: &Path,
    bundle_lib_path: &Path,
    platform_rlib_paths: &[PathBuf],
) -> Result<(), CranelispError> {

    // Get SDK sysroot
    let sysroot_output = Command::new("xcrun")
        .args(["--show-sdk-path"])
        .output()
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to run xcrun: {} (is Xcode Command Line Tools installed?)", e),
            span: (0, 0),
        })?;
    if !sysroot_output.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "xcrun --show-sdk-path failed: {}",
                String::from_utf8_lossy(&sysroot_output.stderr)
            ),
            span: (0, 0),
        });
    }
    let sysroot = String::from_utf8_lossy(&sysroot_output.stdout)
        .trim()
        .to_string();

    // Use relative paths where possible (ld runs from CWD)
    let cwd = std::env::current_dir().unwrap_or_default();
    let rel = |p: &Path| -> String {
        p.strip_prefix(&cwd)
            .unwrap_or(p)
            .to_string_lossy()
            .to_string()
    };

    // Build ld command
    let bundle_dir = bundle_lib_path
        .parent()
        .unwrap_or_else(|| Path::new("."));
    // Extract the library name from the filename: libcranelisp_exe_bundle.a → cranelisp_exe_bundle
    let bundle_stem = bundle_lib_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("cranelisp_exe_bundle");
    let lib_name = bundle_stem.strip_prefix("lib").unwrap_or(bundle_stem);

    let mut ld_args: Vec<String> = vec![
        "-arch".to_string(),
        "arm64".to_string(),
        "-dead_strip".to_string(),
        "-o".to_string(),
        rel(output_path),
        "-e".to_string(),
        "_start".to_string(),
    ];

    // Add startup.o first
    ld_args.push(rel(&startup_o));

    // Add module .o files
    for o_path in module_o_paths {
        ld_args.push(rel(o_path));
    }

    // Add runtime bundle
    ld_args.push(format!("-L{}", rel(bundle_dir)));
    ld_args.push(format!("-l{}", lib_name));

    // Add platform rlibs — ld reads ar archives (rlibs contain .o files with #[export_name] symbols)
    for rlib_path in platform_rlib_paths {
        ld_args.push("-force_load".to_string());
        ld_args.push(rel(rlib_path));
    }

    // Add platform version (required by modern ld)
    ld_args.push("-platform_version".to_string());
    ld_args.push("macos".to_string());
    ld_args.push("14.0".to_string());
    ld_args.push("14.0".to_string());

    // Add system library
    ld_args.push("-lSystem".to_string());
    ld_args.push("-syslibroot".to_string());
    ld_args.push(sysroot);

    // Log a condensed summary: collect unique .o directories as -L paths, show filenames only
    {
        let mut search_dirs: Vec<String> = Vec::new();
        let mut o_names: Vec<String> = Vec::new();
        // startup.o + module .o files
        let all_o: Vec<&Path> = std::iter::once(startup_o)
            .chain(module_o_paths.iter().map(|p| p.as_path()))
            .collect();
        for o in &all_o {
            let r = rel(o);
            let p = Path::new(&r);
            let dir = p.parent().map(|d| d.to_string_lossy().to_string()).unwrap_or_default();
            if !dir.is_empty() && !search_dirs.contains(&dir) {
                search_dirs.push(dir);
            }
            o_names.push(p.file_name().unwrap_or_default().to_string_lossy().to_string());
        }
        let mut lib_args: Vec<String> = Vec::new();
        lib_args.push(format!("-l{}", lib_name));
        for rlib_path in platform_rlib_paths {
            let r = rel(rlib_path);
            let p = Path::new(&r);
            let dir = p.parent().map(|d| d.to_string_lossy().to_string()).unwrap_or_default();
            if !dir.is_empty() && !search_dirs.contains(&dir) {
                search_dirs.push(dir);
            }
            lib_args.push(format!("-force_load {}", p.file_name().unwrap_or_default().to_string_lossy()));
        }
        let dirs_str: String = search_dirs.iter().map(|d| format!(" -L{}", d)).collect();
        eprintln!("; Linking:{} {} {} -o {}", dirs_str, o_names.join(" "), lib_args.join(" "), rel(output_path));
    }

    let ld_output = Command::new("ld")
        .args(&ld_args)
        .output()
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to run ld: {}", e),
            span: (0, 0),
        })?;

    if !ld_output.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "linker failed:\n{}",
                String::from_utf8_lossy(&ld_output.stderr)
            ),
            span: (0, 0),
        });
    }

    Ok(())
}

// ── Platform rlib locator ────────────────────────────────────────────────

/// Find platform rlib paths from loaded module data.
///
/// For each `platform.*` module with a `dll_path`, derives the rlib path
/// by replacing the `.dylib` extension with `.rlib`.
pub fn find_platform_rlibs(
    modules: &HashMap<ModuleFullPath, CompiledModule>,
) -> Vec<PathBuf> {
    let mut rlibs = Vec::new();
    for (mod_path, cm) in modules {
        if !mod_path.0.starts_with("platform.") {
            continue;
        }
        if let Some(dll_path) = &cm.dll_path {
            let rlib_path = dll_path.with_extension("rlib");
            if rlib_path.exists() {
                rlibs.push(rlib_path);
            }
        }
    }
    rlibs
}

// ── Bundle library locator ───────────────────────────────────────────────

/// Find the `libcranelisp_exe_bundle.a` static library.
///
/// Search order:
/// 1. `target/debug/` relative to the cranelisp binary's location
/// 2. `target/release/` relative to the cranelisp binary's location
/// 3. `CRANELISP_BUNDLE_PATH` env var
pub fn find_bundle_lib() -> Result<PathBuf, CranelispError> {
    // Try env var first
    if let Ok(path) = std::env::var("CRANELISP_BUNDLE_PATH") {
        let p = PathBuf::from(path);
        if p.exists() {
            return Ok(p);
        }
    }

    // Try relative to the current executable
    if let Ok(exe_path) = std::env::current_exe() {
        if let Some(exe_dir) = exe_path.parent() {
            // The exe is typically in target/debug/ or target/release/
            // The bundle .a should be in the same directory
            let candidate = exe_dir.join("libcranelisp_exe_bundle.a");
            if candidate.exists() {
                return Ok(candidate);
            }

            // Try sibling directories
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
    }

    Err(CranelispError::CodegenError {
        message: "could not find libcranelisp_exe_bundle.a — \
                  build it with `cargo build -p cranelisp-exe-bundle` or \
                  set CRANELISP_BUNDLE_PATH"
            .to_string(),
        span: (0, 0),
    })
}

// ── Platform manifest name collection ────────────────────────────────

/// Collect platform manifest symbol names from loaded modules.
///
/// For each `platform.*` module, the manifest function is always named
/// `cranelisp_platform_manifest` (generated by the `declare_platform!` macro).
/// Currently only one platform per executable is supported due to this
/// fixed symbol name.
pub fn collect_platform_manifest_names(
    modules: &HashMap<ModuleFullPath, CompiledModule>,
) -> Vec<String> {
    let has_platform = modules
        .keys()
        .any(|mod_path| mod_path.0.starts_with("platform."));
    if has_platform {
        vec!["cranelisp_platform_manifest".to_string()]
    } else {
        vec![]
    }
}

