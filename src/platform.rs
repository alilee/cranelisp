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
use cranelisp_types::{ErrorLocation, 
    CranelispError, DefKind, ModuleEntry, ModuleFullPath, Scheme, Sexp,
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
// the code segment are valid from any thread. The `_library` field is never
// read after construction — only its drop side effect (unloading the DLL) is
// load-bearing. `OwnedPlatformFnDescriptor` fields are `String`/`usize`/`*const`
// and are read-only after manifest parsing. Send+Sync are needed for retention
// in `SharedState::kept_dlls: Mutex<Vec<LoadedPlatform>>`.
unsafe impl Send for LoadedPlatform {}
unsafe impl Sync for LoadedPlatform {}

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
/// Resolve a platform name to a DLL file path.
///
/// Search order per spec §8.11.3:
/// 1. Project root — `{project_root}/platforms/{name}.{ext}`
/// 2. Lib directories — `{lib_dir}/platforms/{name}.{ext}` for each lib dir
/// 3. Platform directories — extra dirs from `CRANELISP_PLATFORM_PATH` env var
///    or explicit programmatic additions
///
/// At each location, tries both `{name}.{ext}` and the Cargo naming convention
/// `libcranelisp_{name}.{ext}`.
pub fn resolve_platform_path(
    name: &str,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    platform_dirs: &[PathBuf],
) -> Option<PathBuf> {
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

    let crate_name = format!("cranelisp_{}", name.replace('-', "_"));

    // Check a single directory for the platform DLL (both naming conventions).
    let check_dir = |dir: &Path| -> Option<PathBuf> {
        // Try plain name: {name}.{ext}
        let candidate = dir.join(format!("{name}.{PLATFORM_EXT}"));
        if candidate.is_file() {
            return Some(candidate);
        }
        // Try Cargo library naming: libcranelisp_{name}.{ext}
        let cargo_candidate = dir.join(format!("lib{crate_name}.{PLATFORM_EXT}"));
        if cargo_candidate.is_file() {
            return Some(cargo_candidate);
        }
        None
    };

    // Tier 1: {project_root}/platforms/
    let root_platforms = project_root.join("platforms");
    if let Some(path) = check_dir(&root_platforms) {
        return Some(path);
    }

    // Tier 2: {lib_dir}/platforms/ for each lib dir.
    for lib_dir in lib_dirs {
        let lib_platforms = lib_dir.join("platforms");
        if let Some(path) = check_dir(&lib_platforms) {
            return Some(path);
        }
    }

    // Tier 3: extra platform directories (from env var, config, or code).
    for dir in platform_dirs {
        if let Some(path) = check_dir(dir) {
            return Some(path);
        }
    }

    None
}

/// Get the user's home directory.
#[allow(dead_code)]
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
    // Per Decision 42 / FIXME 0104: build a fresh `ErrorLocation` per
    // construction site so the user sees the `(platform "name")` form's
    // coordinates.
    let location = || ErrorLocation::from_span_file(span, Some(dll_path.to_path_buf()));

    // Step 1: Open the library.
    let library = unsafe {
        libloading::Library::new(dll_path).map_err(|e| {
            CranelispError::Platform(cranelisp_types::PlatformError::LoadFailed {
                dll: dll_path.to_path_buf(),
                cause: e.to_string(),
                location: location(),
            })
        })?
    };

    // Step 2: Look up the manifest function.
    type ManifestFn = unsafe extern "C" fn(*const HostCallbacks) -> PlatformManifest;
    let manifest_fn: libloading::Symbol<ManifestFn> = unsafe {
        library
            .get(b"cranelisp_platform_manifest")
            .map_err(|_e| {
                CranelispError::Platform(cranelisp_types::PlatformError::ManifestNotFound {
                    dll: dll_path.to_path_buf(),
                    location: location(),
                })
            })?
    };

    // Step 3: Call the manifest function with host callbacks.
    //
    // `alloc_with_tag` is wired to the real intrinsic (S76 W3, FIXME 0229
    // step 1): `cranelisp_intrinsics::cranelisp_alloc_with_tag` allocates a
    // tagged heap ADT (`[total_size][rc=1][tag|pad][fields...]`, returns the
    // alloc base) over `alloc::alloc_with_rc`. This removes the R1 gate —
    // `CLAdt::<T>::construct(...)` no longer panics. `validate_schema` stays
    // at the no-op placeholder: the host has no channel to obtain the DLL's
    // schema text (the macro parses it into a DLL-local `LazyLock<Schema>`
    // and neither invokes `validate_schema` at init nor exposes the literal
    // on the manifest — the S-PLAT-1 seam, blocked on an /arch ruling +
    // platform-crate macro change; see FIXME 0233 step 3).
    let callbacks = HostCallbacks {
        alloc: cranelisp_intrinsics::heap_alloc_payload,
        alloc_with_tag: cranelisp_intrinsics::alloc::cranelisp_alloc_with_tag,
        validate_schema: cranelisp_platform::null_validate_schema,
    };
    let manifest = unsafe { manifest_fn(&callbacks) };

    // Step 4: Validate ABI version.
    if manifest.abi_version != ABI_VERSION {
        return Err(CranelispError::Platform(
            cranelisp_types::PlatformError::AbiVersionMismatch {
                dll: dll_path.to_path_buf(),
                expected: ABI_VERSION,
                found: manifest.abi_version,
                location: location(),
            },
        ));
    }

    // Step 5: Convert to safe Rust types.
    //
    // `manifest_to_descriptors` constructs `PlatformError::LoadFailed` with
    // `ErrorLocation::unknown()` and an empty `dll` path because it has no
    // call-site coordinates; rewrite both at this call site so the user
    // sees the form span.
    let (name, version, descriptors) = unsafe {
        cranelisp_platform::manifest_to_descriptors(&manifest).map_err(|e| match e {
            cranelisp_types::PlatformError::LoadFailed { cause, .. } => {
                CranelispError::Platform(cranelisp_types::PlatformError::LoadFailed {
                    dll: dll_path.to_path_buf(),
                    cause,
                    location: location(),
                })
            }
            // Defensive: forward any non-LoadFailed variant the platform
            // crate may emit in future.
            other => CranelispError::Platform(other),
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
    symbol_tables: &dashmap::DashMap<cranelisp_types::ModuleFullPath, crate::code::SessionSymbolTable>,
    // Retained for caller compatibility; no longer needed now that module
    // creation goes through the types-crate `ensure_module_exists` free fn
    // (W-Absorb) rather than a `TypeCheckEnv`.
    _next_type_id: &std::sync::atomic::AtomicU32,
    _check_state: &mut cranelisp_typecheck::CheckState,
    module_aliases: &cranelisp_types::ModuleAliases,
    platform: &LoadedPlatform,
) -> Result<Vec<(String, *const u8)>, CranelispError> {
    let module_path = ModuleFullPath::from(format!("platform.{}", platform.name));

    // Ensure the platform module exists.
    cranelisp_types::ensure_module_exists(symbol_tables, &module_path);

    // FIXME 0233 step 1: platform sig type-names resolve through the normal
    // symbol-table view + resolution primitive (`check_type_expr`), exactly
    // like program forms — NOT through a bespoke `intrinsic_type_from_name`
    // table. For the leaf names (`Int`/`Bool`/`Float`/`String`) and the `IO`
    // ADT to be reachable from the synthetic `platform.<name>` module, inject
    // the same `(import [primitives [*]])` binding every user module gets
    // (spec §8.8.1; primitives is loaded at session init). Idempotent — a
    // glob-import re-install over an already-imported module is a no-op append.
    inject_primitives_import_for_platform(symbol_tables, &module_path, module_aliases)?;

    let mut jit_symbols: Vec<(String, *const u8)> = Vec::new();

    for desc in &platform.descriptors {
        // Parse + typecheck the signature through the shared frontend +
        // typecheck surface (FIXME 0233 step 1). `parse_type_expr` lowers the
        // one S-expr type form to a `TypeExpr`; `check_type_expr` resolves its
        // leaf names against the `platform.<name>` module's view (primitives
        // imported above), returning the resolved `Type`.
        let ty = parse_and_check_platform_type_sig(
            symbol_tables, module_aliases, &module_path, &desc.type_sig, &desc.name,
        )?;

        let scheme = Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty,
        };

        let param_names: Vec<Symbol> = desc.param_names.iter().map(|n| Symbol::from(n.as_str())).collect();

        // Insert directly into the module's symbol table.
        if let Some(mut table) = symbol_tables.get_mut(&module_path) {
            // D0048 A2 / S70: platform effects are `DefKind::PlatformEffect
            // { scheduling_class }` (the `primitive_kind` / `jit_name` fields
            // retired; the symbol-table key IS the JIT linker name).
            let mut builder = ModuleEntry::def(
                scheme,
                DefKind::PlatformEffect {
                    scheduling_class: desc.scheduling_class,
                },
            )
            .visibility(Visibility::Public)
            .param_names(param_names);
            if !desc.docstring.is_empty() {
                builder = builder.docstring(desc.docstring.clone());
            }
            table.insert(Symbol::from(desc.name.as_str()), builder.build());
        }

        jit_symbols.push((desc.jit_name.clone(), desc.ptr));
    }

    Ok(jit_symbols)
}

/// Inject `(import [primitives [*]])` into the synthetic `platform.<name>`
/// module so platform-sig leaf type-names (`Int`/`Bool`/`Float`/`String` and
/// the `IO` ADT) resolve through the normal symbol-table view, the same way
/// every user module reaches them (spec §8.8.1; FIXME 0233 step 1).
///
/// Idempotent: `install_imports` appends per-symbol `ModuleEntry::Import`
/// bindings; re-installing a glob import over an already-imported module
/// re-writes the same bindings (no duplication hazard for resolution).
fn inject_primitives_import_for_platform(
    symbol_tables: &dashmap::DashMap<cranelisp_types::ModuleFullPath, crate::code::SessionSymbolTable>,
    module_path: &ModuleFullPath,
    module_aliases: &cranelisp_types::ModuleAliases,
) -> Result<(), CranelispError> {
    use cranelisp_types::{ImportNames, ImportSpec};
    let spec = ImportSpec {
        module_path: ModuleFullPath::from("primitives"),
        names: ImportNames::Glob,
        alias: None,
        span: Span::SYNTHETIC,
    };
    crate::imports::install_imports(
        symbol_tables,
        module_path,
        module_aliases,
        std::slice::from_ref(&spec),
    )
}

/// Parse + typecheck a platform function's type signature (FIXME 0233 step 1).
///
/// Replaces the former ad-hoc `parse_platform_type_sig` + `sexp_to_type` +
/// `parse_fn_type` + `parse_io_type` family (which duplicated a subset of the
/// frontend + typecheck type-resolution logic and used a bespoke
/// `intrinsic_type_from_name` table). The signature is one type-expr S-form;
/// `cranelisp_frontend::parse_type_expr` lowers it to a `TypeExpr`, and
/// `cranelisp_typecheck::check_type_expr` resolves its leaf names against the
/// `platform.<name>` module's view (primitives imported by
/// `inject_primitives_import_for_platform`), returning the resolved `Type`.
/// Schema-declared ADT names (`(Fn [Rectangle] Int)`) resolve through the same
/// path once the platform module carries those type defs (host-wiring round-
/// trip; see `design/platform/host-wiring-s76.md` §4 seam 0231/0233).
fn parse_and_check_platform_type_sig(
    symbol_tables: &dashmap::DashMap<cranelisp_types::ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    module_path: &ModuleFullPath,
    sig: &str,
    fn_name: &str,
) -> Result<Type, CranelispError> {
    let expr = cranelisp_frontend::parse_type_expr(sig).map_err(|e| CranelispError::ModuleError {
        message: format!(
            "invalid type signature for platform function '{}': {} ({})",
            fn_name, sig, e
        ),
        location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
    })?;

    let mut ctx = cranelisp_typecheck::SymbolTableAccess::live(symbol_tables, module_path.clone());
    cranelisp_typecheck::check_type_expr(
        &expr,
        &mut ctx,
        symbol_tables,
        module_aliases,
        module_path,
        Span::SYNTHETIC,
    )
    .map_err(|e| CranelispError::ModuleError {
        message: format!(
            "type error in platform function '{}' signature '{}': {}",
            fn_name, sig, e
        ),
        location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
    })
}

/// Check if a Sexp is a `(platform name)` form.
///
/// Sprint 67 hack-back: predicate is currently unused — structural-decl
/// extraction in `worker::extract_module_declarations` inlines the shape
/// check. Retained for symmetry with `extract_platform_name`; narrowed +
/// `#[allow(dead_code)]`.
#[allow(dead_code)]
pub(crate) fn is_platform_form(sexp: &Sexp) -> bool {
    if let Sexp::List(elems, _) = sexp
        && elems.len() == 2
        && let Sexp::Symbol(head, _) = &elems[0]
    {
        return head.as_str() == "platform";
    }
    false
}

/// Extract the platform name from a `(platform name)` form.
///
/// Sprint 67 hack-back: extractor currently unused (call sites inlined into
/// worker decl extraction). Retained for the canonical shape; narrowed +
/// `#[allow(dead_code)]`.
#[allow(dead_code)]
pub(crate) fn extract_platform_name(sexp: &Sexp) -> Option<(String, Span)> {
    if let Sexp::List(elems, span) = sexp
        && elems.len() == 2
        && let Sexp::Symbol(head, _) = &elems[0]
        && head.as_str() == "platform"
        && let Sexp::Symbol(name, _) = &elems[1]
    {
        return Some((name.to_string(), *span));
    }
    None
}

/// Full platform loading pipeline: resolve path, load DLL, validate manifest,
/// register in typechecker.
///
/// Returns the loaded platform (must be kept alive) and JIT symbols to register.
#[allow(clippy::type_complexity, clippy::too_many_arguments)]
pub fn load_and_register_platform(
    symbol_tables: &dashmap::DashMap<cranelisp_types::ModuleFullPath, crate::code::SessionSymbolTable>,
    next_type_id: &std::sync::atomic::AtomicU32,
    check_state: &mut cranelisp_typecheck::CheckState,
    module_aliases: &cranelisp_types::ModuleAliases,
    platform_name: &str,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    platform_dirs: &[PathBuf],
    span: Span,
) -> Result<(LoadedPlatform, Vec<(String, *const u8)>), CranelispError> {
    // Step 1: Resolve the DLL path (§8.11.3).
    let dll_path = resolve_platform_path(platform_name, project_root, lib_dirs, platform_dirs)
        .ok_or_else(|| {
            CranelispError::ModuleError {
                message: format!("platform '{}' not found", platform_name),
                location: ErrorLocation::from_span_file(span, None),
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
            location: ErrorLocation::from_span_file(span, Some(dll_path)),
        });
    }

    // Step 4: Register in typechecker.
    let jit_symbols = register_platform_in_tc(
        symbol_tables, next_type_id, check_state, module_aliases, &platform,
    )?;

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
        let result = resolve_platform_path("./nonexistent.dylib", Path::new("."), &[], &[]);
        assert!(result.is_none()); // File doesn't exist, so None.
    }

    // -----------------------------------------------------------------
    // Host-side ADT marshaling — alloc_with_tag wiring (FIXME 0229 step 1).
    //
    // These tests pin the int-side wiring: a `HostCallbacks` constructed
    // exactly as `load_platform_dll` builds it must carry the REAL
    // `cranelisp_alloc_with_tag` intrinsic in its `alloc_with_tag` field
    // (not the R1-gate `null_alloc_with_tag` panic placeholder), and
    // invoking that field as a platform DLL would (via `CLAdt::construct`)
    // must produce the heap layout `CLAdt::read_tag`/`read_field` expect:
    // `[total_size | rc=1 | tag@HEAP_HEADER_SIZE | f0@+8 | f1@+16 ...]`,
    // returning the alloc BASE pointer. This is the int-side half of the
    // round-trip; the platform crate unit-tests the CLAdt read path
    // (adt.rs T9–T13) and the intrinsic crate unit-tests the layout
    // (alloc.rs `test_alloc_with_tag_*`).
    // -----------------------------------------------------------------

    /// Build the `HostCallbacks` exactly as `load_platform_dll` does, so the
    /// test exercises the wiring under test rather than a hand-built struct.
    fn wired_host_callbacks() -> HostCallbacks {
        HostCallbacks {
            alloc: cranelisp_intrinsics::heap_alloc_payload,
            alloc_with_tag: cranelisp_intrinsics::alloc::cranelisp_alloc_with_tag,
            validate_schema: cranelisp_platform::null_validate_schema,
        }
    }

    // spec: design/platform/host-wiring-s76.md §2 — the host wires the real
    // alloc_with_tag intrinsic; the R1 gate (null_alloc_with_tag panic) is
    // gone. A two-field ADT constructed through the callback round-trips:
    // tag + both fields read back at the documented offsets, RC = 1.
    #[test]
    fn alloc_with_tag_callback_round_trips_two_field_adt() {
        let callbacks = wired_host_callbacks();
        let fields: [i64; 2] = [0x0BAD_F00D_DEAD_BEEFu64 as i64, -42];

        // Invoke as a platform DLL would (CLAdt::construct → alloc_with_tag).
        let base = (callbacks.alloc_with_tag)(2, 2, fields.as_ptr());
        assert_ne!(base, 0, "wired callback must return a non-null alloc base");

        let header = cranelisp_types::HeapHeader::SIZE as i64;
        // SAFETY: `base` is a freshly allocated tagged-ADT base pointer; the
        // layout (total_size, rc, tag, fields) is the documented contract.
        unsafe {
            let total_size = *(base as *const i64);
            // 16 header + 8 tag slot + 2*8 fields = 40.
            assert_eq!(total_size, 40, "total_size = header + tag + 2 fields");
            let rc = *((base + 8) as *const i64);
            assert_eq!(rc, 1, "alloc_with_rc initialises RC to 1");
            // Tag at payload+0 (base + HEAP_HEADER_SIZE) reads back as i64.
            let tag = *((base + header) as *const i64);
            assert_eq!(tag, 2, "variant tag at payload+0");
            // Fields at payload+8 and payload+16 — copied verbatim.
            let f0 = *((base + header + 8) as *const i64);
            let f1 = *((base + header + 16) as *const i64);
            assert_eq!(f0, fields[0], "field 0 copied verbatim");
            assert_eq!(f1, fields[1], "field 1 copied verbatim");
        }

        // Free via the runtime dealloc (reads total_size from the header).
        cranelisp_intrinsics::alloc::heap_dealloc(base);
    }

    // spec: design/platform/host-wiring-s76.md §2 — a nullary-shaped data
    // constructor (zero fields) round-trips through the wired callback:
    // tag-only payload, RC = 1, alloc base returned (not the R1 panic).
    #[test]
    fn alloc_with_tag_callback_round_trips_zero_field_adt() {
        let callbacks = wired_host_callbacks();
        let base = (callbacks.alloc_with_tag)(7, 0, std::ptr::null());
        assert_ne!(base, 0);

        let header = cranelisp_types::HeapHeader::SIZE as i64;
        // SAFETY: documented tagged-ADT layout for a zero-field constructor.
        unsafe {
            let total_size = *(base as *const i64);
            assert_eq!(total_size, 24, "total_size = 16 header + 8 tag slot");
            let tag = *((base + header) as *const i64);
            assert_eq!(tag, 7);
        }
        cranelisp_intrinsics::alloc::heap_dealloc(base);
    }

    // (FIXME 0233 step 1) The ad-hoc `parse_platform_type_sig` + `sexp_to_type`
    // family — and their two unit tests `test_parse_fn_type_sig` /
    // `test_parse_zero_param_type_sig` — were deleted. Platform-sig parsing is
    // now `cranelisp_frontend::parse_type_expr` (unit-tested in frontend) +
    // `cranelisp_typecheck::check_type_expr` (unit-tested in typecheck); the
    // integrated platform-sig resolution path is exercised e2e by
    // `tests/spec_platforms.rs::platform_form_with_stdio_compiles_in_run_mode`
    // and `::io_trampoline_executes_print_to_stdout` (both load the stdio DLL
    // and resolve its `(Fn [String] (IO Unit))`-shaped sigs through this path).

    // spec: platform-dlls §search — tier 2 project-local resolution
    #[test]
    fn test_resolve_platform_path_local() {
        let dir = tempfile::tempdir().unwrap();
        let platforms_dir = dir.path().join("platforms");
        std::fs::create_dir_all(&platforms_dir).unwrap();

        let dll_file = platforms_dir.join(format!("test-plat.{PLATFORM_EXT}"));
        std::fs::write(&dll_file, b"fake dll").unwrap();

        let result = resolve_platform_path("test-plat", dir.path(), &[], &[]);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), dll_file);
    }

    // spec: platform-dlls §8.11.3 — extra platform_dirs (tier 3)
    #[test]
    fn test_resolve_platform_path_extra_dir() {
        let dir = tempfile::tempdir().unwrap();
        let extra_dir = dir.path().join("extra-platforms");
        std::fs::create_dir_all(&extra_dir).unwrap();

        let dll_file = extra_dir.join(format!("libcranelisp_stdio.{PLATFORM_EXT}"));
        std::fs::write(&dll_file, b"fake dll").unwrap();

        let result = resolve_platform_path("stdio", dir.path(), &[], &[extra_dir]);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), dll_file);
    }

    // spec: platform-dlls §8.11.3 — tier 1 (project root) takes priority over tier 3
    #[test]
    fn test_resolve_platform_path_local_priority() {
        let dir = tempfile::tempdir().unwrap();

        // Create both tier 1 (project root) and tier 3 (extra dir) files.
        let platforms_dir = dir.path().join("platforms");
        std::fs::create_dir_all(&platforms_dir).unwrap();
        let local_dll = platforms_dir.join(format!("stdio.{PLATFORM_EXT}"));
        std::fs::write(&local_dll, b"local").unwrap();

        let extra_dir = dir.path().join("extra");
        std::fs::create_dir_all(&extra_dir).unwrap();
        let extra_dll = extra_dir.join(format!("libcranelisp_stdio.{PLATFORM_EXT}"));
        std::fs::write(&extra_dll, b"extra").unwrap();

        let result = resolve_platform_path("stdio", dir.path(), &[], &[extra_dir]);
        assert_eq!(result.unwrap(), local_dll); // Tier 1 wins.
    }

    // spec: platform-dlls §8.11.3 — not found returns None
    #[test]
    fn test_resolve_platform_path_not_found() {
        let dir = tempfile::tempdir().unwrap();
        let result = resolve_platform_path("nonexistent", dir.path(), &[], &[]);
        assert!(result.is_none());
    }

    // spec: 10-io §10.9.1 — load stdio platform DLL and validate manifest
    #[test]
    fn test_load_stdio_platform_dll() {
        // This test requires the stdio platform DLL to be built.
        // cargo build -p cranelisp-stdio must have run.
        let project_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let target_debug = project_root.join("target/debug");
        let dll_path = resolve_platform_path("stdio", project_root, &[], &[target_debug]);
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
        let target_debug = project_root.join("target/debug");
        let dll_path = resolve_platform_path("stdio", project_root, &[], &[target_debug.clone()]);
        if dll_path.is_none() {
            eprintln!("skipping test: stdio platform DLL not built");
            return;
        }

        let symbol_tables = dashmap::DashMap::new();
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let user_mod = ModuleFullPath::from("user");
        symbol_tables.insert(user_mod.clone(), crate::code::SessionSymbolTable::new_with_params(user_mod.clone()));
        crate::bootstrap::mount_synthetic_modules(&symbol_tables, &next_type_id);
        let mut check_state = cranelisp_typecheck::CheckState::new(user_mod);
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let (platform, jit_symbols) = load_and_register_platform(
            &symbol_tables,
            &next_type_id,
            &mut check_state,
            &module_aliases,
            "stdio",
            project_root,
            &[],
            &[target_debug],
            Span::SYNTHETIC,
        ).unwrap();

        // Should have registered 2 JIT symbols (print, read-line).
        assert_eq!(jit_symbols.len(), 2);

        // Check the platform.stdio module exists and has the functions.
        let module_path = ModuleFullPath::from("platform.stdio");
        let table = symbol_tables.get(&module_path);
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
                    assert!(matches!(ret.as_ref(), Type::ADT(name, _) if name.name.as_ref() == "IO"));
                }
                _ => panic!("expected Fn type for print"),
            }
            assert!(matches!(kind.as_ref(), DefKind::PlatformEffect { .. }));
            assert!(docstring.is_some());
        } else {
            panic!("expected Def entry for print");
        }

        // Platform should be kept alive.
        assert_eq!(platform.name, "stdio");
    }

    // spec: §8.11.5 — assemble_platform_dirs reads CRANELISP_PLATFORM_PATH
    #[test]
    fn test_assemble_platform_dirs_env_var() {
        let dir = tempfile::tempdir().unwrap();
        let env_dir = dir.path().join("custom-platforms");
        std::fs::create_dir_all(&env_dir).unwrap();

        let dll_file = env_dir.join(format!("test-env.{PLATFORM_EXT}"));
        std::fs::write(&dll_file, b"fake dll").unwrap();

        // Set the env var temporarily.
        let prev = std::env::var("CRANELISP_PLATFORM_PATH").ok();
        unsafe { std::env::set_var("CRANELISP_PLATFORM_PATH", env_dir.to_str().unwrap()) };

        // assemble_platform_dirs picks up the env var.
        let platform_dirs = crate::session::assemble_platform_dirs();
        let result = resolve_platform_path("test-env", dir.path(), &[], &platform_dirs);
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
        let target_debug = project_root.join("target/debug");
        let dll_path = resolve_platform_path("stdio", project_root, &[], &[target_debug.clone()]);
        if dll_path.is_none() {
            eprintln!("skipping test: stdio platform DLL not built");
            return;
        }

        let symbol_tables = dashmap::DashMap::new();
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let user_mod = ModuleFullPath::from("user");
        symbol_tables.insert(user_mod.clone(), crate::code::SessionSymbolTable::new_with_params(user_mod.clone()));
        let mut check_state = cranelisp_typecheck::CheckState::new(user_mod);
        let module_aliases = cranelisp_types::ModuleAliases::default();
        // Try to load with wrong name — manifest says "stdio" but we say "wrong-name"
        let result = load_and_register_platform(
            &symbol_tables,
            &next_type_id,
            &mut check_state,
            &module_aliases,
            "wrong-name",
            project_root,
            &[],
            &[target_debug],
            Span::SYNTHETIC,
        );

        // This won't match because resolve_platform_path("wrong-name") won't find
        // the stdio DLL. So we'll get a "not found" error instead.
        assert!(result.is_err());
    }
}
