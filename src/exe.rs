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

use cranelisp_types::{
    CranelispError, ModuleEntry, Span, SymbolTable, Type,
};
#[cfg(test)]
use cranelisp_types::ModuleFullPath;

// Re-export generate_startup_object from the backend for convenience.
pub use cranelisp_backend::exe::generate_startup_object;

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
pub fn validate_main(entry_symbols: &SymbolTable) -> Result<MainReturnKind, CranelispError> {
    let entry = entry_symbols.get("main").ok_or_else(|| {
        CranelispError::CodegenError {
            message: "entry module has no 'main' function".to_string(),
            span: Span::SYNTHETIC,
        }
    })?;

    match entry {
        ModuleEntry::Def { scheme, .. } => classify_main_return_type(&scheme.ty),
        _ => Err(CranelispError::CodegenError {
            message: "'main' in entry module is not a function definition".to_string(),
            span: Span::SYNTHETIC,
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
                span: Span::SYNTHETIC,
            }),
        },
        _ => Err(CranelispError::CodegenError {
            message: format!(
                "main must be a zero-argument function, found: {}",
                type_display_brief(ty)
            ),
            span: Span::SYNTHETIC,
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

// ── Linker configuration ────────────────────────────────────────────────

/// Platform-specific linker configuration.
///
/// Only macOS aarch64 is implemented for Ring 4. The abstraction exists so
/// that Linux ELF support can be added later without restructuring.
struct LinkerConfig {
    arch: &'static str,
    entry_symbol: &'static str,
    platform: &'static str,
    min_version: &'static str,
    sdk_version: &'static str,
}

impl LinkerConfig {
    /// Configuration for the current host. Currently macOS aarch64 only.
    fn for_host() -> Result<Self, CranelispError> {
        if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            Ok(LinkerConfig {
                arch: "arm64",
                entry_symbol: "_start",
                platform: "macos",
                min_version: "14.0",
                sdk_version: "14.0",
            })
        } else {
            Err(CranelispError::CodegenError {
                message: "standalone executable generation is only supported on macOS aarch64"
                    .to_string(),
                span: Span::SYNTHETIC,
            })
        }
    }
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
    let sysroot = get_sdk_sysroot()?;

    // Extract bundle directory and library name
    let bundle_dir = bundle_lib_path
        .parent()
        .unwrap_or_else(|| Path::new("."));
    let bundle_stem = bundle_lib_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("cranelisp_exe_bundle");
    let lib_name = bundle_stem.strip_prefix("lib").unwrap_or(bundle_stem);

    let mut ld_args: Vec<String> = vec![
        "-arch".to_string(),
        config.arch.to_string(),
        "-dead_strip".to_string(),
        "-o".to_string(),
        output_path.to_string_lossy().to_string(),
        "-e".to_string(),
        config.entry_symbol.to_string(),
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
    ld_args.push(config.platform.to_string());
    ld_args.push(config.min_version.to_string());
    ld_args.push(config.sdk_version.to_string());

    // System library and SDK root
    ld_args.push("-lSystem".to_string());
    ld_args.push("-syslibroot".to_string());
    ld_args.push(sysroot);

    // Log a condensed summary
    log_link_summary(
        output_path,
        startup_o_path,
        module_o_paths,
        lib_name,
        platform_rlib_paths,
    );

    // Invoke the linker
    let ld_output = Command::new("ld")
        .args(&ld_args)
        .output()
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to run ld: {e}"),
            span: Span::SYNTHETIC,
        })?;

    if !ld_output.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "linker failed:\n{}",
                String::from_utf8_lossy(&ld_output.stderr)
            ),
            span: Span::SYNTHETIC,
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
            span: Span::SYNTHETIC,
        })?;

    if !output.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "xcrun --show-sdk-path failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ),
            span: Span::SYNTHETIC,
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

/// Find platform rlib paths.
///
/// Currently returns an empty list. When platform linking is implemented,
/// this will query loaded platform modules for their rlib paths.
pub fn find_platform_rlibs() -> Vec<PathBuf> {
    // TODO: When platform modules are implemented, discover rlib paths
    // from the loaded platform registry.
    Vec::new()
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
        span: Span::SYNTHETIC,
    })
}

// ── Platform manifest name collection ───────────────────────────────────

/// Collect platform manifest symbol names.
///
/// Currently returns an empty list. When platform modules are implemented,
/// this will query the loaded platform registry.
pub fn collect_platform_manifest_names() -> Vec<String> {
    // TODO: When platform modules are implemented, discover manifest names
    // from the loaded platform registry.
    Vec::new()
}

// ── Tests ───────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{DefKind, Scheme, Symbol, TypeName, Visibility};
    use std::collections::HashMap;

    fn make_main_entry(ty: Type) -> ModuleEntry {
        ModuleEntry::Def {
            scheme: Scheme {
                vars: vec![],
                constraints: HashMap::new(),
                ty,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn { constrained_fn: None }),
            callees: Vec::new(),
            got_slot: None,
            trait_origin: None,
            ast: None,
        }
    }

    // spec: design/backend/executable-generation.md §7 — main :: () -> Int accepted
    #[test]
    fn validate_main_returns_int() {
        let mut st = SymbolTable::new(ModuleFullPath::from("user"));
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
        let mut st = SymbolTable::new(ModuleFullPath::from("user"));
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
        let st = SymbolTable::new(ModuleFullPath::from("user"));
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
        let mut st = SymbolTable::new(ModuleFullPath::from("user"));
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
        let mut st = SymbolTable::new(ModuleFullPath::from("user"));
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

    // spec: design/backend/executable-generation.md — platform rlib discovery (empty)
    #[test]
    fn find_platform_rlibs_empty() {
        let rlibs = find_platform_rlibs();
        assert!(rlibs.is_empty());
    }

    // spec: design/backend/executable-generation.md — platform manifest collection (empty)
    #[test]
    fn collect_platform_manifest_names_empty() {
        let names = collect_platform_manifest_names();
        assert!(names.is_empty());
    }

    // spec: design/backend/executable-generation.md §5 — LinkerConfig for macOS
    #[test]
    fn linker_config_for_host() {
        if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            let config = LinkerConfig::for_host().unwrap();
            assert_eq!(config.arch, "arm64");
            assert_eq!(config.entry_symbol, "_start");
        }
    }
}
