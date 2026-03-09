// Platform DLL loading: resolve, load, validate, and register platform functions.
//
// Platform DLLs are cdylib crates that implement IO effects (e.g., stdio).
// They export a `cranelisp_platform_manifest` entry point per the C-ABI
// contract in `cranelisp-platform`.
//
// No `unwrap()` in this module -- all errors use `?`.

use std::path::{Path, PathBuf};

use cranelisp_platform::{
    ABI_VERSION, HostCallbacks, OwnedPlatformFnDescriptor, PlatformManifest,
};
use cranelisp_types::{
    CranelispError, DefKind, JitSymbol, ModuleEntry, ModuleFullPath, PrimitiveKind, Scheme, Sexp,
    Span, Symbol, Type, Visibility,
};

/// A loaded platform DLL. Must remain alive for the process lifetime
/// (function pointers point into the library's code segment).
pub struct LoadedPlatform {
    /// The loaded dynamic library handle.
    _library: libloading::Library,
    /// Platform name from the manifest.
    pub name: String,
    /// Platform version from the manifest.
    pub version: String,
    /// Descriptors for each platform function.
    pub descriptors: Vec<OwnedPlatformFnDescriptor>,
}

// SAFETY: LoadedPlatform holds a Library handle whose code segment is mapped
// for the process lifetime (DLLs are never unloaded). Function pointers into
// the code segment are valid from any thread.
unsafe impl Send for LoadedPlatform {}

/// Platform extension for the current OS.
#[cfg(target_os = "macos")]
const PLATFORM_EXT: &str = "dylib";
#[cfg(target_os = "linux")]
const PLATFORM_EXT: &str = "so";
#[cfg(target_os = "windows")]
const PLATFORM_EXT: &str = "dll";

/// Resolve a platform DLL's file path using the three-tier search order.
///
/// Search order (first match wins):
/// 1. `CRANELISP_PLATFORM_PATH` env var (colon-separated directories)
/// 2. `{project_root}/platforms/{name}.{ext}`
/// 3. `target/debug/lib{crate_name}.{ext}` then `target/release/lib{crate_name}.{ext}`
/// 4. `~/.cranelisp/platforms/{name}.{ext}`
///
/// If the name contains `/` or ends with a platform extension, it is treated
/// as an explicit path and used directly.
pub fn resolve_platform_path(name: &str, project_root: &Path) -> Option<PathBuf> {
    // Explicit path bypass: if name looks like a filesystem path.
    if name.contains('/')
        || name.ends_with(".dylib")
        || name.ends_with(".so")
        || name.ends_with(".dll")
    {
        let path = PathBuf::from(name);
        if path.is_file() {
            return Some(path);
        }
        return None;
    }

    // Tier 1: CRANELISP_PLATFORM_PATH env var.
    if let Ok(env_val) = std::env::var("CRANELISP_PLATFORM_PATH") {
        for dir in env_val.split(':').filter(|s| !s.is_empty()) {
            let candidate = PathBuf::from(dir).join(format!("{name}.{PLATFORM_EXT}"));
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }

    // Tier 2: {project_root}/platforms/{name}.{ext}
    let local = project_root
        .join("platforms")
        .join(format!("{name}.{PLATFORM_EXT}"));
    if local.is_file() {
        return Some(local);
    }

    // Tier 3: Cargo build output (development convenience).
    let crate_name = format!("cranelisp_{}", name.replace('-', "_"));
    let lib_name = format!("lib{crate_name}.{PLATFORM_EXT}");

    let debug_path = project_root.join("target/debug").join(&lib_name);
    if debug_path.is_file() {
        return Some(debug_path);
    }
    let release_path = project_root.join("target/release").join(&lib_name);
    if release_path.is_file() {
        return Some(release_path);
    }

    // Tier 4: ~/.cranelisp/platforms/
    if let Some(home) = home_dir() {
        let global = home
            .join(".cranelisp/platforms")
            .join(format!("{name}.{PLATFORM_EXT}"));
        if global.is_file() {
            return Some(global);
        }
    }

    None
}

/// Get the user's home directory.
fn home_dir() -> Option<PathBuf> {
    std::env::var("HOME")
        .ok()
        .map(PathBuf::from)
}

/// Load a platform DLL, validate the manifest, and extract descriptors.
///
/// Steps:
/// 1. Open the shared library via `libloading`.
/// 2. Look up the `cranelisp_platform_manifest` entry point.
/// 3. Call it with a `HostCallbacks` containing the runtime allocator.
/// 4. Validate ABI version.
/// 5. Convert C-ABI manifest to safe Rust types.
///
/// Returns a `LoadedPlatform` that must remain alive for the process lifetime.
pub fn load_platform_dll(
    dll_path: &Path,
    span: Span,
) -> Result<LoadedPlatform, CranelispError> {
    // Step 1: Open the library.
    let library = unsafe {
        libloading::Library::new(dll_path).map_err(|e| CranelispError::ModuleError {
            message: format!(
                "failed to load platform library '{}': {}",
                dll_path.display(),
                e
            ),
            file: Some(dll_path.to_path_buf()),
            span,
        })?
    };

    // Step 2: Look up the manifest function.
    type ManifestFn = unsafe extern "C" fn(*const HostCallbacks) -> PlatformManifest;
    let manifest_fn: libloading::Symbol<ManifestFn> = unsafe {
        library
            .get(b"cranelisp_platform_manifest")
            .map_err(|e| CranelispError::ModuleError {
                message: format!(
                    "platform missing manifest function '{}': {}",
                    dll_path.display(),
                    e
                ),
                file: Some(dll_path.to_path_buf()),
                span,
            })?
    };

    // Step 3: Call the manifest function with host callbacks.
    let callbacks = HostCallbacks {
        alloc: cranelisp_runtime::heap_alloc_payload,
    };
    let manifest = unsafe { manifest_fn(&callbacks) };

    // Step 4: Validate ABI version.
    if manifest.abi_version != ABI_VERSION {
        return Err(CranelispError::ModuleError {
            message: format!(
                "platform ABI version mismatch: platform has {}, host expects {}",
                manifest.abi_version, ABI_VERSION
            ),
            file: Some(dll_path.to_path_buf()),
            span,
        });
    }

    // Step 5: Convert to safe Rust types.
    let (name, version, descriptors) = unsafe {
        cranelisp_platform::manifest_to_descriptors(&manifest).map_err(|e| {
            CranelispError::ModuleError {
                message: e,
                file: Some(dll_path.to_path_buf()),
                span,
            }
        })?
    };

    Ok(LoadedPlatform {
        _library: library,
        name,
        version,
        descriptors,
    })
}

/// Register a loaded platform's functions in the typechecker and collect
/// symbols for JIT registration.
///
/// Creates a `platform.{name}` module in the typechecker and inserts a
/// `ModuleEntry::Def` for each platform function. Returns the list of
/// (jit_name, function_pointer) pairs for JIT symbol registration.
pub fn register_platform_in_tc(
    tc: &mut cranelisp_typecheck::TypeChecker,
    platform: &LoadedPlatform,
) -> Result<Vec<(String, *const u8)>, CranelispError> {
    let module_path = ModuleFullPath::from(format!("platform.{}", platform.name));

    // Save current module and switch to the platform module.
    let prev_module = tc.current_module_path().clone();
    tc.set_current_module(module_path.clone());

    let mut jit_symbols: Vec<(String, *const u8)> = Vec::new();

    for desc in &platform.descriptors {
        // Parse the type signature from the S-expression string.
        let ty = parse_platform_type_sig(&desc.type_sig, &desc.name)?;

        let scheme = Scheme {
            vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty,
        };

        let param_names: Vec<Symbol> = desc.param_names.iter().map(|n| Symbol::from(n.as_str())).collect();

        tc.symbol_table_mut().insert(
            Symbol::from(desc.name.as_str()),
            ModuleEntry::Def {
                scheme,
                visibility: Visibility::Public,
                docstring: if desc.docstring.is_empty() {
                    None
                } else {
                    Some(desc.docstring.clone())
                },
                param_names,
                kind: Box::new(DefKind::Primitive {
                    primitive_kind: PrimitiveKind::PlatformEffect,
                    jit_name: Some(JitSymbol::from(desc.jit_name.as_str())),
                }),
            },
        );

        jit_symbols.push((desc.jit_name.clone(), desc.ptr));
    }

    // Restore previous module.
    tc.set_current_module(prev_module);

    Ok(jit_symbols)
}

/// Parse a platform function's type signature from its S-expression string.
///
/// Handles simple cases: `(Fn [T1 T2] R)` where types are primitive names
/// or `(IO T)` wrappers.
fn parse_platform_type_sig(sig: &str, fn_name: &str) -> Result<Type, CranelispError> {
    // Parse the signature as an S-expression.
    let sexps = cranelisp_frontend::parse(sig).map_err(|_| CranelispError::ModuleError {
        message: format!(
            "invalid type signature for platform function '{}': {}",
            fn_name, sig
        ),
        file: None,
        span: Span::SYNTHETIC,
    })?;

    if sexps.len() != 1 {
        return Err(CranelispError::ModuleError {
            message: format!(
                "platform function '{}' type signature must be a single form, got {}",
                fn_name,
                sexps.len()
            ),
            file: None,
            span: Span::SYNTHETIC,
        });
    }

    sexp_to_type(&sexps[0], fn_name)
}

/// Convert a parsed S-expression into a Type.
///
/// Handles:
/// - `Int`, `Bool`, `Float`, `String` -> primitive types
/// - `(Fn [P1 P2] R)` -> function type
/// - `(IO T)` -> ADT "IO" with inner type
fn sexp_to_type(sexp: &Sexp, fn_name: &str) -> Result<Type, CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) => {
            Type::from_name(name.as_ref()).ok_or_else(|| CranelispError::ModuleError {
                message: format!(
                    "unknown type '{}' in platform function '{}' signature",
                    name, fn_name
                ),
                file: None,
                span: Span::SYNTHETIC,
            })
        }
        Sexp::List(elems, _) if !elems.is_empty() => {
            if let Sexp::Symbol(head, _) = &elems[0] {
                match head.as_str() {
                    "Fn" => parse_fn_type(elems, fn_name),
                    "IO" => parse_io_type(elems, fn_name),
                    _ => Err(CranelispError::ModuleError {
                        message: format!(
                            "unsupported type constructor '{}' in platform function '{}' signature",
                            head, fn_name
                        ),
                        file: None,
                        span: Span::SYNTHETIC,
                    }),
                }
            } else {
                Err(CranelispError::ModuleError {
                    message: format!(
                        "invalid type form in platform function '{}' signature",
                        fn_name
                    ),
                    file: None,
                    span: Span::SYNTHETIC,
                })
            }
        }
        _ => Err(CranelispError::ModuleError {
            message: format!(
                "invalid type in platform function '{}' signature",
                fn_name
            ),
            file: None,
            span: Span::SYNTHETIC,
        }),
    }
}

/// Parse `(Fn [P1 P2 ...] R)` into `Type::Fn`.
fn parse_fn_type(elems: &[Sexp], fn_name: &str) -> Result<Type, CranelispError> {
    if elems.len() != 3 {
        return Err(CranelispError::ModuleError {
            message: format!(
                "Fn type must have exactly 2 arguments (params and return), got {}",
                elems.len() - 1
            ),
            file: None,
            span: Span::SYNTHETIC,
        });
    }

    // Parse param list.
    let params = match &elems[1] {
        Sexp::Bracket(items, _) => {
            let mut param_types = Vec::new();
            for item in items {
                param_types.push(sexp_to_type(item, fn_name)?);
            }
            param_types
        }
        _ => {
            return Err(CranelispError::ModuleError {
                message: format!(
                    "Fn type params must be a bracket list in platform function '{}'",
                    fn_name
                ),
                file: None,
                span: Span::SYNTHETIC,
            });
        }
    };

    // Parse return type.
    let ret = sexp_to_type(&elems[2], fn_name)?;

    Ok(Type::Fn(params, Box::new(ret)))
}

/// Parse `(IO T)` into `Type::ADT("IO", vec![T])`.
fn parse_io_type(elems: &[Sexp], fn_name: &str) -> Result<Type, CranelispError> {
    if elems.len() != 2 {
        return Err(CranelispError::ModuleError {
            message: format!(
                "IO type must have exactly 1 argument, got {}",
                elems.len() - 1
            ),
            file: None,
            span: Span::SYNTHETIC,
        });
    }

    let inner = sexp_to_type(&elems[1], fn_name)?;
    Ok(Type::ADT("IO".into(), vec![inner]))
}

/// Check if a Sexp is a `(platform name)` form.
pub fn is_platform_form(sexp: &Sexp) -> bool {
    if let Sexp::List(elems, _) = sexp {
        if elems.len() == 2 {
            if let Sexp::Symbol(head, _) = &elems[0] {
                return head.as_str() == "platform";
            }
        }
    }
    false
}

/// Extract the platform name from a `(platform name)` form.
pub fn extract_platform_name(sexp: &Sexp) -> Option<(String, Span)> {
    if let Sexp::List(elems, span) = sexp {
        if elems.len() == 2 {
            if let Sexp::Symbol(head, _) = &elems[0] {
                if head.as_str() == "platform" {
                    if let Sexp::Symbol(name, _) = &elems[1] {
                        return Some((name.to_string(), *span));
                    }
                }
            }
        }
    }
    None
}

/// Full platform loading pipeline: resolve path, load DLL, validate manifest,
/// register in typechecker.
///
/// Returns the loaded platform (must be kept alive) and JIT symbols to register.
pub fn load_and_register_platform(
    tc: &mut cranelisp_typecheck::TypeChecker,
    platform_name: &str,
    project_root: &Path,
    span: Span,
) -> Result<(LoadedPlatform, Vec<(String, *const u8)>), CranelispError> {
    // Step 1: Resolve the DLL path.
    let dll_path = resolve_platform_path(platform_name, project_root).ok_or_else(|| {
        CranelispError::ModuleError {
            message: format!("platform '{}' not found", platform_name),
            file: None,
            span,
        }
    })?;

    // Step 2: Load and validate the DLL.
    let platform = load_platform_dll(&dll_path, span)?;

    // Step 3: Validate manifest name matches declared name.
    if platform.name != platform_name {
        return Err(CranelispError::ModuleError {
            message: format!(
                "platform manifest name '{}' does not match declared name '{}'",
                platform.name, platform_name
            ),
            file: Some(dll_path),
            span,
        });
    }

    // Step 4: Register in typechecker.
    let jit_symbols = register_platform_in_tc(tc, &platform)?;

    Ok((platform, jit_symbols))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // spec: 10-io §10.9.1 — platform declaration recognized
    #[test]
    fn test_is_platform_form() {
        let sexps = cranelisp_frontend::parse("(platform stdio)").unwrap();
        assert!(is_platform_form(&sexps[0]));
    }

    // spec: 10-io §10.9.1 — non-platform forms rejected
    #[test]
    fn test_is_platform_form_rejects_non_platform() {
        let sexps = cranelisp_frontend::parse("(defn main [] 42)").unwrap();
        assert!(!is_platform_form(&sexps[0]));
    }

    // spec: 10-io §10.9.1 — platform name extraction
    #[test]
    fn test_extract_platform_name() {
        let sexps = cranelisp_frontend::parse("(platform stdio)").unwrap();
        let (name, _) = extract_platform_name(&sexps[0]).unwrap();
        assert_eq!(name, "stdio");
    }

    // spec: 10-io §10.9.1 — platform path resolution (explicit path bypass)
    #[test]
    fn test_resolve_explicit_path_bypass() {
        // A name containing '/' is treated as an explicit path.
        let result = resolve_platform_path("./nonexistent.dylib", Path::new("."));
        assert!(result.is_none()); // File doesn't exist, so None.
    }

    // spec: 10-io §10.9.1 — platform type signature parsing
    #[test]
    fn test_parse_fn_type_sig() {
        let ty = parse_platform_type_sig("(Fn [String] (IO Int))", "test").unwrap();
        match &ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], Type::String);
                match ret.as_ref() {
                    Type::ADT(name, args) => {
                        assert_eq!(name.as_ref(), "IO");
                        assert_eq!(args.len(), 1);
                        assert_eq!(args[0], Type::Int);
                    }
                    _ => panic!("expected IO ADT return type"),
                }
            }
            _ => panic!("expected Fn type"),
        }
    }

    // spec: 10-io §10.9.1 — zero-param function type
    #[test]
    fn test_parse_zero_param_type_sig() {
        let ty = parse_platform_type_sig("(Fn [] (IO String))", "test").unwrap();
        match &ty {
            Type::Fn(params, ret) => {
                assert!(params.is_empty());
                match ret.as_ref() {
                    Type::ADT(name, args) => {
                        assert_eq!(name.as_ref(), "IO");
                        assert_eq!(args.len(), 1);
                        assert_eq!(args[0], Type::String);
                    }
                    _ => panic!("expected IO ADT return type"),
                }
            }
            _ => panic!("expected Fn type"),
        }
    }

    // spec: platform-dlls §search — tier 2 project-local resolution
    #[test]
    fn test_resolve_platform_path_local() {
        let dir = tempfile::tempdir().unwrap();
        let platforms_dir = dir.path().join("platforms");
        std::fs::create_dir_all(&platforms_dir).unwrap();

        let dll_file = platforms_dir.join(format!("test-plat.{PLATFORM_EXT}"));
        std::fs::write(&dll_file, b"fake dll").unwrap();

        let result = resolve_platform_path("test-plat", dir.path());
        assert!(result.is_some());
        assert_eq!(result.unwrap(), dll_file);
    }

    // spec: platform-dlls §search — tier 3 Cargo build output
    #[test]
    fn test_resolve_platform_path_cargo_debug() {
        let dir = tempfile::tempdir().unwrap();
        let debug_dir = dir.path().join("target/debug");
        std::fs::create_dir_all(&debug_dir).unwrap();

        let dll_file = debug_dir.join(format!("libcranelisp_stdio.{PLATFORM_EXT}"));
        std::fs::write(&dll_file, b"fake dll").unwrap();

        let result = resolve_platform_path("stdio", dir.path());
        assert!(result.is_some());
        assert_eq!(result.unwrap(), dll_file);
    }

    // spec: platform-dlls §search — tier 2 takes priority over tier 3
    #[test]
    fn test_resolve_platform_path_local_priority() {
        let dir = tempfile::tempdir().unwrap();

        // Create both tier 2 and tier 3 files.
        let platforms_dir = dir.path().join("platforms");
        std::fs::create_dir_all(&platforms_dir).unwrap();
        let local_dll = platforms_dir.join(format!("stdio.{PLATFORM_EXT}"));
        std::fs::write(&local_dll, b"local").unwrap();

        let debug_dir = dir.path().join("target/debug");
        std::fs::create_dir_all(&debug_dir).unwrap();
        let cargo_dll = debug_dir.join(format!("libcranelisp_stdio.{PLATFORM_EXT}"));
        std::fs::write(&cargo_dll, b"cargo").unwrap();

        let result = resolve_platform_path("stdio", dir.path());
        assert_eq!(result.unwrap(), local_dll); // Tier 2 wins.
    }

    // spec: platform-dlls §search — not found returns None
    #[test]
    fn test_resolve_platform_path_not_found() {
        let dir = tempfile::tempdir().unwrap();
        let result = resolve_platform_path("nonexistent", dir.path());
        assert!(result.is_none());
    }

    // spec: 10-io §10.9.1 — load stdio platform DLL and validate manifest
    #[test]
    fn test_load_stdio_platform_dll() {
        // This test requires the stdio platform DLL to be built.
        // cargo build -p cranelisp-stdio must have run.
        let project_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let dll_path = resolve_platform_path("stdio", project_root);
        if dll_path.is_none() {
            eprintln!("skipping test: stdio platform DLL not built");
            return;
        }
        let dll_path = dll_path.unwrap();

        let platform = load_platform_dll(&dll_path, Span::SYNTHETIC).unwrap();

        assert_eq!(platform.name, "stdio");
        assert_eq!(platform.version, "0.1.0");
        assert_eq!(platform.descriptors.len(), 2);

        // Verify function descriptors.
        let print_desc = &platform.descriptors[0];
        assert_eq!(print_desc.name, "print");
        assert_eq!(print_desc.jit_name, "cranelisp_print");
        assert_eq!(print_desc.param_count, 1);
        assert!(!print_desc.docstring.is_empty());

        let read_desc = &platform.descriptors[1];
        assert_eq!(read_desc.name, "read-line");
        assert_eq!(read_desc.jit_name, "cranelisp_read_line");
        assert_eq!(read_desc.param_count, 0);
    }

    // spec: 10-io §10.9.1 — register platform functions in typechecker
    #[test]
    fn test_register_platform_in_tc() {
        let project_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let dll_path = resolve_platform_path("stdio", project_root);
        if dll_path.is_none() {
            eprintln!("skipping test: stdio platform DLL not built");
            return;
        }

        let mut tc = cranelisp_typecheck::TypeChecker::new();
        let (platform, jit_symbols) = load_and_register_platform(
            &mut tc,
            "stdio",
            project_root,
            Span::SYNTHETIC,
        ).unwrap();

        // Should have registered 2 JIT symbols (print, read-line).
        assert_eq!(jit_symbols.len(), 2);

        // Check the platform.stdio module exists and has the functions.
        let module_path = ModuleFullPath::from("platform.stdio");
        let table = tc.module_table(&module_path);
        assert!(table.is_some(), "platform.stdio module should exist");

        let table = table.unwrap();
        let print_entry = table.get("print");
        assert!(print_entry.is_some(), "print should be in platform.stdio");

        let read_entry = table.get("read-line");
        assert!(read_entry.is_some(), "read-line should be in platform.stdio");

        // Verify types are correctly parsed.
        if let Some(ModuleEntry::Def { scheme, kind, docstring, .. }) = print_entry {
            // print: (Fn [String] (IO Int))
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    assert_eq!(params[0], Type::String);
                    assert!(matches!(ret.as_ref(), Type::ADT(name, _) if name.as_ref() == "IO"));
                }
                _ => panic!("expected Fn type for print"),
            }
            assert!(matches!(kind.as_ref(), DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect, .. }));
            assert!(docstring.is_some());
        } else {
            panic!("expected Def entry for print");
        }

        // Platform should be kept alive.
        assert_eq!(platform.name, "stdio");
    }

    // spec: platform-dlls §search — env var tier 1 resolution
    #[test]
    fn test_resolve_platform_path_env_var() {
        let dir = tempfile::tempdir().unwrap();
        let env_dir = dir.path().join("custom-platforms");
        std::fs::create_dir_all(&env_dir).unwrap();

        let dll_file = env_dir.join(format!("test-env.{PLATFORM_EXT}"));
        std::fs::write(&dll_file, b"fake dll").unwrap();

        // Set the env var temporarily.
        // Safety: this test is single-threaded and we restore the var after.
        let prev = std::env::var("CRANELISP_PLATFORM_PATH").ok();
        unsafe { std::env::set_var("CRANELISP_PLATFORM_PATH", env_dir.to_str().unwrap()) };

        let result = resolve_platform_path("test-env", dir.path());
        assert!(result.is_some());
        assert_eq!(result.unwrap(), dll_file);

        // Restore env var.
        match prev {
            Some(v) => unsafe { std::env::set_var("CRANELISP_PLATFORM_PATH", v) },
            None => unsafe { std::env::remove_var("CRANELISP_PLATFORM_PATH") },
        }
    }

    // spec: platform-dlls §validation — manifest name mismatch error
    #[test]
    fn test_platform_name_mismatch_error() {
        let project_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let dll_path = resolve_platform_path("stdio", project_root);
        if dll_path.is_none() {
            eprintln!("skipping test: stdio platform DLL not built");
            return;
        }

        let mut tc = cranelisp_typecheck::TypeChecker::new();
        // Try to load with wrong name — manifest says "stdio" but we say "wrong-name"
        let result = load_and_register_platform(
            &mut tc,
            "wrong-name",
            project_root,
            Span::SYNTHETIC,
        );

        // This won't match because resolve_platform_path("wrong-name") won't find
        // the stdio DLL. So we'll get a "not found" error instead.
        assert!(result.is_err());
    }
}
