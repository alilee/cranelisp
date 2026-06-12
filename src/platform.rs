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
/// (function pointers point into the library's code segment, and the
/// exported GOT slab lives in the DLL's writable data segment).
pub struct LoadedPlatform {
    /// The loaded dynamic library handle.
    _library: libloading::Library,
    /// Platform name from the manifest.
    pub name: String,
    /// Platform version from the manifest.
    pub version: String,
    /// Descriptors for each platform function.
    pub descriptors: Vec<OwnedPlatformFnDescriptor>,
    /// The address of the DLL's exported GOT slab
    /// (`__cranelisp_got_platform_<name>`), already populated by the manifest
    /// fn (manifest order IS GOT slot order, platform-interface.md §5.1). The
    /// host wraps this in place via `GotTable::with_static_backing` — no copy
    /// (§5.3, §6.4). Lifetime = the dlopen handle (`_library`), kept for the
    /// session in `SharedState::kept_dlls`. `None` only if the symbol was
    /// absent (a pre-GOT-export DLL — load aborts before this is consulted).
    pub got_base: *const std::sync::atomic::AtomicPtr<u8>,
    /// The DLL's exported layout-hash string
    /// (`__cranelisp_layout_hash_<name>`), or `None` if the platform declared
    /// no schema (scalar-only platform — first-build/absent tolerated,
    /// §5.5.4). Used by the load-time hash gate.
    pub layout_hash: Option<String>,
}

// SAFETY: LoadedPlatform holds a Library handle whose code+data segments are
// mapped for the process lifetime (DLLs are never unloaded). Function pointers
// into the code segment, and the `got_base` pointer into the DLL's writable
// GOT slab, are valid from any thread. The `_library` field is never read after
// construction — only its drop side effect (unloading the DLL) is load-bearing.
// `OwnedPlatformFnDescriptor` fields are `String`/`usize`/`*const` and are
// read-only after manifest parsing; `got_base` is a stable slab address (the
// slab's `AtomicPtr` slots provide their own interior synchronisation).
// Send+Sync are needed for retention in
// `SharedState::kept_dlls: Mutex<Vec<LoadedPlatform>>`.
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

/// Validate a DLL's declared ABI version against the host's `ABI_VERSION`.
///
/// Extracted from `load_platform_dll` (Step 4) as the smallest testable owner
/// of the `manifest.abi_version != ABI_VERSION` branch — `load_platform_dll`
/// itself dlopens a real DLL, so the comparison cannot otherwise be exercised
/// with a perturbed version (platform-interface.md §5.2; the manifest's
/// `abi_version` is a C-ABI fact the host checks at load). Returns
/// `PlatformError::AbiVersionMismatch { expected, found }` on mismatch (both
/// values populated so the user message names the host's expected version and
/// the DLL's stale one), `Ok(())` on match. Minimum mechanism, no behaviour
/// change — the load path and the unit test call the same branch.
fn check_abi_version(
    found: u32,
    dll_path: &Path,
    location: ErrorLocation,
) -> Result<(), CranelispError> {
    if found != ABI_VERSION {
        return Err(CranelispError::Platform(
            cranelisp_types::PlatformError::AbiVersionMismatch {
                dll: dll_path.to_path_buf(),
                expected: ABI_VERSION,
                found,
                location,
            },
        ));
    }
    Ok(())
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
    // `CLAdt::<T>::construct(...)` no longer panics. The `validate_schema`
    // callback channel is gone (FIXME 0288): schema validation is superseded
    // by the layout-hash gate (§5.5.4) — the host regenerates the schema from
    // its live tables and compares the canonical hash to the DLL's exported
    // `__cranelisp_layout_hash_<name>`. Calling the manifest fn ALSO populates
    // the DLL's exported GOT slab (manifest order IS GOT slot order, §5.1),
    // which we dlsym below.
    let callbacks = HostCallbacks {
        alloc: cranelisp_intrinsics::heap_alloc_payload,
        alloc_with_tag: cranelisp_intrinsics::alloc::cranelisp_alloc_with_tag,
    };
    let manifest = unsafe { manifest_fn(&callbacks) };

    // Step 4: Validate ABI version.
    check_abi_version(manifest.abi_version, dll_path, location())?;

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

    // Step 6: dlsym the exported GOT slab + the layout-hash data symbol
    // (platform-interface.md §5.1, §5.5.4, §6.4). The manifest fn above
    // populated the GOT slab (slot i = functions[i]'s fn ptr). The host wraps
    // it in place (`GotTable::with_static_backing`) in `register_platform_in_tc`
    // — no copy; lifetime = this dlopen handle, kept on `SharedState::kept_dlls`.
    let got_sym_name = format!("__cranelisp_got_platform_{name}");
    let got_base = unsafe {
        let sym: libloading::Symbol<*const std::sync::atomic::AtomicPtr<u8>> = library
            .get(got_sym_name.as_bytes())
            .map_err(|_e| {
                CranelispError::Platform(cranelisp_types::PlatformError::LoadFailed {
                    dll: dll_path.to_path_buf(),
                    cause: format!(
                        "platform DLL does not export its GOT symbol '{got_sym_name}' \
                         (rebuild the platform with the current declare_platform! macro)"
                    ),
                    location: location(),
                })
            })?;
        // The exported symbol is the array `[AtomicPtr<u8>; GOT_TABLE_SIZE]`;
        // `Symbol` derefs to a pointer-to-the-array's-first-element. Take the
        // raw element address (the slab base).
        *sym
    };

    // The layout-hash export is optional (scalar-only platforms declare no
    // schema; first builds tolerated, §5.5.4).
    let layout_hash_sym_name = format!("__cranelisp_layout_hash_{name}");
    let layout_hash: Option<String> = unsafe {
        library
            .get::<*const &str>(layout_hash_sym_name.as_bytes())
            .ok()
            .map(|sym| (**sym).to_string())
    };

    Ok(LoadedPlatform {
        _library: library,
        name,
        version,
        descriptors,
        got_base,
        layout_hash,
    })
}

/// Register a loaded platform's functions in the host symbol tables.
///
/// Creates the `platform.{name}` module and inserts a `ModuleEntry::Def` per
/// platform function, with `got_slot = manifest index` and the scheme resolved
/// from the FQ sig. The module's `GotTable` WRAPS the DLL's exported GOT slab
/// in place (`GotTable::with_static_backing` — no copy; the dlopen handle on
/// `SharedState::kept_dlls` keeps it alive), so GOT-indirect dispatch reaches
/// the platform fns identically to any user/stdlib module (platform-interface.md
/// §5.3, §6.4). No imports are injected (FQ sigs, §5.3); the old
/// `(jit_name, ptr)` / `JITBuilder::symbol` direct-extern path is gone — fn
/// pointers live in the GOT, dispatched GOT-indirect.
pub fn register_platform_in_tc(
    symbol_tables: &dashmap::DashMap<cranelisp_types::ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    platform: &LoadedPlatform,
) -> Result<(), CranelispError> {
    let module_path = ModuleFullPath::from(format!("platform.{}", platform.name));

    // Ensure the platform module exists, then WRAP the DLL's exported GOT slab
    // in place as the module's GOT (platform-interface.md §5.3 / §6.4 — no
    // copy). The slab was populated by the manifest fn at load (slot i =
    // functions[i]'s fn ptr); `got_data_symbol_name("platform.<name>")` ==
    // `__cranelisp_got_platform_<name>` matches the DLL's exported symbol, so
    // `Jit::new`'s per-module GOT registration (jit.rs step 2) wires the
    // GOT-indirect data symbol to this slab base for free.
    cranelisp_types::ensure_module_exists(symbol_tables, &module_path);
    {
        // SAFETY: `got_base` is the address of the DLL's exported
        // `[AtomicPtr<u8>; GOT_TABLE_SIZE]` static (`__cranelisp_got_platform_<name>`),
        // populated by the manifest fn. The DLL handle is retained for the
        // session (`SharedState::kept_dlls`), so the slab is `'static`-valid for
        // every reader of the resulting `GotTable`. `with_static_backing`'s
        // contract (one backing per slab; writable section for the trace swap;
        // exactly `GOT_TABLE_SIZE` slots) is satisfied by the macro-emitted
        // static (`#[export_name]` writable `__DATA` array of that exact type).
        let slab: &'static [std::sync::atomic::AtomicPtr<u8>; cranelisp_types::GOT_TABLE_SIZE] =
            unsafe { &*(platform.got_base as *const _) };
        let got = std::sync::Arc::new(cranelisp_types::GotTable::with_static_backing(slab));
        if let Some(mut table) = symbol_tables.get_mut(&module_path) {
            table.got = got;
            // The platform GOT's slots are owned by the DLL; the host never
            // allocates into it. Advance `next_got_slot` past the manifest so a
            // later host allocation (if any) cannot collide with a platform slot.
            table.next_got_slot = platform.descriptors.len();
        }
    }

    for (slot, desc) in platform.descriptors.iter().enumerate() {
        // Parse + typecheck the FQ signature through the shared frontend +
        // typecheck surface. `parse_type_expr` lowers the one S-expr type form
        // to a `TypeExpr`; `check_type_expr` resolves its FQ leaf names
        // (`primitives/Int`, `shapes/Rectangle`) directly against the named
        // modules (auto-loaded per FIXME 0268) — NO injected imports (§5.3).
        let ty = parse_and_check_platform_type_sig(
            symbol_tables, module_aliases, &module_path, &desc.type_sig, &desc.name,
        )?;

        // FIXME 0318 / spec §8.11: a platform fn MUST return `IO _`. Foreign
        // native code's purity is unverifiable — the compiler can only trust the
        // declared signature — so a platform fn typed pure would be memoized /
        // reordered / elided / sparked under lenient eval while the host does
        // arbitrary effects: unsound. The only sound treatment of foreign code is
        // to sequence its effects, which the `IO` return type forces.
        require_io_return(&ty, &platform.name, &desc.name)?;

        let scheme = Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty,
        };

        let param_names: Vec<Symbol> = desc.param_names.iter().map(|n| Symbol::from(n.as_str())).collect();

        // Insert directly into the module's symbol table with `got_slot =
        // manifest index` (§5.3) — the GOT-indirect dispatch arm in backend
        // (`apply.rs`) activates on `got_slot: Some(_)`.
        if let Some(mut table) = symbol_tables.get_mut(&module_path) {
            let mut builder = ModuleEntry::def(
                scheme,
                DefKind::PlatformEffect {
                    scheduling_class: desc.scheduling_class,
                },
            )
            .visibility(Visibility::Public)
            .got_slot(slot)
            .param_names(param_names);
            if !desc.docstring.is_empty() {
                builder = builder.docstring(desc.docstring.clone());
            }
            table.insert(Symbol::from(desc.name.as_str()), builder.build());
        }
    }

    Ok(())
}

/// Inject `(import [primitives [*]])` into the synthetic `platform.<name>`
/// module so platform-sig leaf type-names (`Int`/`Bool`/`Float`/`String` and
/// the `IO` ADT) resolve through the normal symbol-table view, the same way
/// every user module reaches them (spec §8.8.1; FIXME 0233 step 1).
///
/// Idempotent: `install_imports` appends per-symbol `ModuleEntry::Import`
/// bindings; re-installing a glob import over an already-imported module
/// re-writes the same bindings (no duplication hazard for resolution).
/// Normalise FQ leaf names the frontend type-expr parser leaves under-qualified.
///
/// `cranelisp_frontend::parse_type_expr` (`build_type_expr`) lowers a slashed
/// type leaf with the WHOLE slashed string in one field:
/// - `primitives/String` is classified by its post-slash leaf (`String`,
///   uppercase) as a type, but `build_type_expr`/`parse_annotation_name` puts
///   the whole string into the leaf so a leading-lowercase form parses to
///   `TypeExpr::TypeVar("primitives/String")` (a free type variable);
/// - `shapes/Rectangle` parses uppercase-first to
///   `TypeExpr::Named(TypeRef { module: None, name: "shapes/Rectangle" })`.
///
/// In BOTH cases the slashed module prefix sits inside the leaf string, NOT in
/// `TypeRef.module`. `check_type_expr`'s resolver builds its lookup key from
/// `tref.module` + `tref.name` (qualified only when `module: Some(_)`), so a
/// `module: None` node whose `name` literally contains a slash is looked up as
/// a type named `"shapes/Rectangle"` in module `''` — which never resolves
/// (Root B-shapes, FIXME 0321). This pass re-partitions every such slashed leaf
/// (in `TypeVar`, `Named`, and `Applied` heads) into
/// `TypeRef { module: Some(prefix), name: leaf }` via `split_slashed_type_ref`,
/// so the resolver names the module directly.
///
/// This is the int-side bridge for the FQ-sig design (platform-interface.md §5.3)
/// — frontend type-expr parsing of `module/Type` leaves is a separate concern
/// (the parser change is FIXME 0230's neighbourhood). Keeping the normalisation
/// at the platform boundary avoids a frontend change for this cut.
fn fqize_type_expr(expr: cranelisp_types::TypeExpr) -> cranelisp_types::TypeExpr {
    use cranelisp_types::TypeExpr;
    match expr {
        // `primitives/String` parses lowercase-first → `TypeVar`; a slashed leaf
        // with an uppercase post-slash name is really a qualified TYPE. Split it.
        TypeExpr::TypeVar(name) => match split_slashed_type_ref(name.as_ref()) {
            Some(tref) => TypeExpr::Named(tref),
            None => TypeExpr::TypeVar(name),
        },
        // `shapes/Rectangle` parses uppercase-first (the reader classifies on the
        // post-slash leaf) → `Named(TypeRef { module: None, name:
        // "shapes/Rectangle" })` — the WHOLE slashed string lands in `name`.
        // `check_type_expr`'s resolver builds its lookup key from `tref.module` +
        // `tref.name`, so an un-split `name` names a type literally called
        // `"shapes/Rectangle"` in module `''` (never resolves). Re-partition the
        // slash into `{ module: Some("shapes"), name: "Rectangle" }`.
        TypeExpr::Named(tref) => match split_slashed_type_ref(tref.name.as_ref()) {
            Some(split) => TypeExpr::Named(split),
            None => TypeExpr::Named(tref),
        },
        TypeExpr::FnType(params, ret) => TypeExpr::FnType(
            params.into_iter().map(fqize_type_expr).collect(),
            Box::new(fqize_type_expr(*ret)),
        ),
        TypeExpr::Applied(head, args) => {
            // The applied head may itself be slashed (`(option/Option Int)`);
            // re-partition it, and recurse into the type arguments.
            let head = split_slashed_type_ref(head.name.as_ref()).unwrap_or(head);
            TypeExpr::Applied(head, args.into_iter().map(fqize_type_expr).collect())
        }
        other => other,
    }
}

/// Re-partition a slashed type-leaf string (`shapes/Rectangle`) into a
/// `TypeRef { module: Some("shapes"), name: "Rectangle" }`, matching the
/// `TypeRef` doc convention (`(option/Option Int)` →
/// `{ module: Some("option"), name: "Option" }`). Returns `None` when the
/// string carries no `/` or its post-slash leaf is not an uppercase TYPE (a
/// type variable, not a type) — the caller keeps the node unchanged.
///
/// This mirrors `cranelisp_types::resolve::split_qualified` (crate-private
/// there), kept inline at the platform boundary so the FQ-leaf repair does not
/// reach across the int→types edge for a one-line split.
fn split_slashed_type_ref(name: &str) -> Option<cranelisp_types::TypeRef> {
    use cranelisp_types::{ModuleFullPath, TypeName, TypeRef};
    let (module_part, leaf) = name.split_once('/')?;
    if leaf.chars().next().is_some_and(|c| c.is_uppercase()) {
        Some(TypeRef::new(Some(ModuleFullPath::from(module_part)), TypeName::from(leaf)))
    } else {
        None
    }
}

/// Parse + typecheck a platform function's FQ type signature.
///
/// The signature is one type-expr S-form with FQ leaf refs
/// (`primitives/Int`, `shapes/Rectangle`); `cranelisp_frontend::parse_type_expr`
/// lowers it to a `TypeExpr`, `fqize_type_expr` repairs under-qualified leaves
/// the parser left as type-vars, and `cranelisp_typecheck::check_type_expr`
/// resolves the FQ leaf names directly against the named modules (auto-loaded
/// per FIXME 0268), returning the resolved `Type`. NO imports are injected into
/// the platform module (platform-interface.md §5.3) — the sigs are FQ.
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
    let expr = fqize_type_expr(expr);

    let mut ctx = cranelisp_typecheck::SymbolTableAccess::live(symbol_tables, module_path.clone());
    // Platform type signatures are FULLY QUALIFIED (`primitives/Int`,
    // `shapes/Rectangle`; platform-interface.md §5.3 — NO injected imports),
    // so the prelude bare-name outer-scope fallback (S78 §2.7) never fires
    // here. An empty map (all-OFF) is the correct, complete input.
    let prelude_fallback = cranelisp_typecheck::PreludeFallback::default();
    cranelisp_typecheck::check_type_expr(
        &expr,
        &mut ctx,
        symbol_tables,
        module_aliases,
        &prelude_fallback,
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

/// Enforce that a platform fn's checked type returns `IO _` (FIXME 0318 / spec
/// §8.11 — "Platform functions MUST return `IO _`").
///
/// `ty` is the platform fn's resolved type. The acceptable shape is a function
/// whose return type is the `IO` ADT (`(Fn [..] (IO a))`); a zero-param IO value
/// (`(IO a)` with no `Fn` wrapper) is also accepted defensively. Anything else —
/// a pure return (`(Fn [..] Int)`), or a non-`IO` ADT return — is rejected with a
/// diagnostic naming the platform, the function, and the requirement.
///
/// Rationale (FIXME 0318): foreign native code's purity is unverifiable, so the
/// compiler must trust the declared signature; the only sound treatment of a
/// foreign effect is to sequence it, which `IO` forces. Every existing platform
/// (`stdio`, `test-capture`) already returns `IO _`, so this is low-ripple.
fn require_io_return(ty: &Type, platform_name: &str, fn_name: &str) -> Result<(), CranelispError> {
    let ret = match ty {
        Type::Fn(_, ret) => ret.as_ref(),
        other => other,
    };
    let is_io = matches!(ret, Type::ADT(name, _) if name.name.as_ref() == "IO");
    if is_io {
        return Ok(());
    }
    Err(CranelispError::ModuleError {
        message: format!(
            "platform function '{platform_name}/{fn_name}' must return `IO _` \
             (declared signature is not IO); every platform function MUST return \
             `IO _` because foreign code's purity is unverifiable — the compiler \
             trusts the declared signature, so a non-IO platform fn would be \
             treated as pure (memoized, reordered, elided) while the host performs \
             effects. Wrap the return in IO."
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
/// register in the host symbol tables (GOT wrapped in place, got_slot = manifest
/// index, FQ sigs — no injected imports, no jit_name registration).
///
/// Returns the loaded platform; the caller MUST keep it alive (retain on
/// `SharedState::kept_dlls`) so the wrapped GOT slab + fn pointers stay valid.
#[allow(clippy::too_many_arguments)]
pub fn load_and_register_platform(
    symbol_tables: &dashmap::DashMap<cranelisp_types::ModuleFullPath, crate::code::SessionSymbolTable>,
    module_aliases: &cranelisp_types::ModuleAliases,
    platform_name: &str,
    project_root: &Path,
    lib_dirs: &[PathBuf],
    platform_dirs: &[PathBuf],
    span: Span,
) -> Result<LoadedPlatform, CranelispError> {
    // Step 1: Resolve the DLL path (§8.11.3).
    let dll_path = resolve_platform_path(platform_name, project_root, lib_dirs, platform_dirs)
        .ok_or_else(|| {
            CranelispError::ModuleError {
                message: format!("platform '{}' not found", platform_name),
                location: ErrorLocation::from_span_file(span, None),
            }
        })?;

    // Step 2: Load and validate the DLL (dlsym GOT + layout-hash).
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

    // Step 4: Register in the host symbol tables (GOT wrap + FQ sigs).
    register_platform_in_tc(symbol_tables, module_aliases, &platform)?;

    Ok(platform)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------
    // FIXME 0318 / spec §8.11 — every platform fn MUST return `IO _`.
    // `require_io_return` is the smallest testable owner of the gate
    // `register_platform_in_tc` applies after the sig is checked (the full
    // path dlopens a real DLL; this drives the rejection with a perturbed
    // sig type, no DLL needed — the check is on the resolved return type).
    // -----------------------------------------------------------------

    fn io_int() -> Type {
        Type::ADT(
            cranelisp_types::FQTypeName::new(
                ModuleFullPath::from("primitives"),
                cranelisp_types::TypeName::from("IO"),
            ),
            vec![Type::Int],
        )
    }

    // spec: design/arch/fixmes/0318 / spec §8.11 — a platform fn declaring a
    // non-IO return (`(Fn [Int] Int)`) is REJECTED, naming the platform + fn +
    // the IO requirement.
    #[test]
    fn platform_fn_non_io_return_is_rejected() {
        let pure_sig = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let err = require_io_return(&pure_sig, "shapes", "area")
            .expect_err("a non-IO platform fn sig must be rejected");
        match err {
            CranelispError::ModuleError { message, .. } => {
                assert!(message.contains("shapes/area"), "names platform/fn: {message}");
                assert!(message.contains("IO"), "names the IO requirement: {message}");
            }
            other => panic!("expected ModuleError, got {other:?}"),
        }
    }

    // spec: design/arch/fixmes/0318 / spec §8.11 — an IO-returning platform fn
    // (`(Fn [String] (IO Int))`, the stdio `print` shape) passes the gate.
    #[test]
    fn platform_fn_io_return_accepted() {
        let io_sig = Type::Fn(vec![Type::String], Box::new(io_int()));
        assert!(
            require_io_return(&io_sig, "stdio", "print").is_ok(),
            "an IO-returning platform fn must pass the gate"
        );
    }

    // spec: design/arch/fixmes/0318 — a non-IO ADT return (e.g. a bare
    // `shapes/Rectangle`) is also rejected — only the `IO` ADT satisfies the gate.
    #[test]
    fn platform_fn_non_io_adt_return_is_rejected() {
        let rect = Type::ADT(
            cranelisp_types::FQTypeName::new(
                ModuleFullPath::from("shapes"),
                cranelisp_types::TypeName::from("Rectangle"),
            ),
            vec![],
        );
        let sig = Type::Fn(vec![Type::Int], Box::new(rect));
        assert!(
            require_io_return(&sig, "shapes", "make").is_err(),
            "a non-IO ADT return must be rejected"
        );
    }

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

    // -----------------------------------------------------------------
    // ABI-version-mismatch detection (platform-interface.md §5.2) — drives the
    // WIRED `manifest.abi_version != ABI_VERSION` branch with a perturbed
    // version, without dlopening a real DLL (load_platform_dll owns the dlopen;
    // check_abi_version is the smallest testable owner of the branch).
    // -----------------------------------------------------------------

    // spec: design/arch/platform-interface.md §5.2 — a DLL whose declared ABI
    // version differs from the host's `ABI_VERSION` is refused with
    // PlatformError::AbiVersionMismatch carrying BOTH the expected (host) and
    // found (DLL) versions correct.
    #[test]
    fn abi_version_mismatch_detected() {
        let dll = Path::new("/fake/stale-abi.dylib");
        let perturbed = ABI_VERSION + 1;
        let err = check_abi_version(perturbed, dll, ErrorLocation::unknown())
            .expect_err("a perturbed ABI version must be refused");
        match err {
            CranelispError::Platform(cranelisp_types::PlatformError::AbiVersionMismatch {
                expected,
                found,
                ..
            }) => {
                assert_eq!(expected, ABI_VERSION, "expected = host ABI_VERSION");
                assert_eq!(found, perturbed, "found = the DLL's declared version");
            }
            other => panic!("expected AbiVersionMismatch, got {other:?}"),
        }
    }

    // spec: design/arch/platform-interface.md §5.2 — a DLL declaring the host's
    // own `ABI_VERSION` passes the gate (Ok). Guards that check_abi_version's
    // extraction did not change behaviour on the happy path.
    #[test]
    fn abi_version_match_accepts() {
        let dll = Path::new("/fake/ok.dylib");
        assert!(
            check_abi_version(ABI_VERSION, dll, ErrorLocation::unknown()).is_ok(),
            "the host's own ABI_VERSION must pass the gate"
        );
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

        // Verify function descriptors. Platform fns carry no exported linker
        // name (jit_name retired, FIXME 0288) — dispatch is GOT-indirect at the
        // manifest index.
        let print_desc = &platform.descriptors[0];
        assert_eq!(print_desc.name, "print");
        assert_eq!(print_desc.param_count, 1);
        assert!(!print_desc.docstring.is_empty());

        let read_desc = &platform.descriptors[1];
        assert_eq!(read_desc.name, "read-line");
        assert_eq!(read_desc.param_count, 0);

        // The DLL must export its GOT slab (dlsym'd at load).
        assert!(!platform.got_base.is_null(), "platform must export its GOT");
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
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let platform = load_and_register_platform(
            &symbol_tables,
            &module_aliases,
            "stdio",
            project_root,
            &[],
            &[target_debug],
            Span::SYNTHETIC,
        ).unwrap();

        // Check the platform.stdio module exists and has the functions.
        let module_path = ModuleFullPath::from("platform.stdio");
        let table = symbol_tables.get(&module_path);
        assert!(table.is_some(), "platform.stdio module should exist");

        let table = table.unwrap();
        let print_entry = table.get("print");
        assert!(print_entry.is_some(), "print should be in platform.stdio");

        let read_entry = table.get("read-line");
        assert!(read_entry.is_some(), "read-line should be in platform.stdio");

        // Verify types are correctly parsed AND `got_slot = manifest index`
        // (platform-interface.md §5.3) — the GOT-indirect dispatch activator.
        if let Some(ModuleEntry::Def { scheme, kind, docstring, got_slot, .. }) = print_entry {
            // print: (Fn [primitives/String] (primitives/IO primitives/Int))
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
            assert_eq!(*got_slot, Some(0), "print is manifest index 0");
        } else {
            panic!("expected Def entry for print");
        }
        if let Some(ModuleEntry::Def { got_slot, .. }) = read_entry {
            assert_eq!(*got_slot, Some(1), "read-line is manifest index 1");
        }

        // The platform module's GOT wraps the DLL's exported slab; slot 0 (print)
        // must be a live (non-null) fn pointer after the manifest populated it.
        assert!(
            !table.got.load_slot(0).is_null(),
            "platform GOT slot 0 must be populated by the DLL manifest"
        );

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
        let user_mod = ModuleFullPath::from("user");
        symbol_tables.insert(user_mod.clone(), crate::code::SessionSymbolTable::new_with_params(user_mod.clone()));
        let module_aliases = cranelisp_types::ModuleAliases::default();
        // Try to load with wrong name — manifest says "stdio" but we say "wrong-name"
        let result = load_and_register_platform(
            &symbol_tables,
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

    // -----------------------------------------------------------------
    // FQ type-leaf split (Root B-shapes, FIXME 0321) — the platform sig
    // FQ-leaf repair MUST re-partition a slashed type leaf into
    // `TypeRef { module: Some(prefix), name: leaf }`, not leave the whole
    // slashed string in `name` with `module: None` (which `check_type_expr`
    // looks up as a type literally named `"shapes/Rectangle"` in module `''`).
    // -----------------------------------------------------------------

    // spec: design/arch/platform-interface.md §5.3 — FQ sig leaf partition
    #[test]
    fn split_slashed_type_ref_partitions_module_and_name() {
        let tref = split_slashed_type_ref("shapes/Rectangle")
            .expect("an uppercase post-slash leaf is a qualified type");
        assert_eq!(tref.module, Some(ModuleFullPath::from("shapes")));
        assert_eq!(tref.name.as_ref(), "Rectangle");
    }

    // spec: design/arch/platform-interface.md §5.3 — multi-component module path
    #[test]
    fn split_slashed_type_ref_keeps_full_module_path() {
        let tref = split_slashed_type_ref("core.option/Option")
            .expect("dotted module path is preserved as the module part");
        assert_eq!(tref.module, Some(ModuleFullPath::from("core.option")));
        assert_eq!(tref.name.as_ref(), "Option");
    }

    // spec: design/arch/platform-interface.md §5.3 — a non-slashed name or a
    // lowercase post-slash leaf (a type variable, e.g. `a` / `m/a`) is NOT a
    // qualified type and is left for the caller to keep unchanged.
    #[test]
    fn split_slashed_type_ref_rejects_non_type_leaves() {
        assert!(split_slashed_type_ref("Rectangle").is_none(), "no slash → no split");
        assert!(split_slashed_type_ref("a").is_none(), "bare type var → no split");
        assert!(
            split_slashed_type_ref("m/a").is_none(),
            "lowercase post-slash leaf is a type variable, not a type"
        );
    }

    // spec: design/arch/platform-interface.md §5.3 — `fqize_type_expr` repairs
    // the WHOLE platform sig: a slashed leaf in a `Named` node (the production
    // shape — `build_type_expr` classifies `shapes/Rectangle` as uppercase and
    // emits `Named(TypeRef { module: None, name: "shapes/Rectangle" })`) is
    // re-partitioned; a `primitives/Int`-shaped `TypeVar` is lifted to a split
    // `Named`. Drives the exact `area` sig from the `shapes` fixture.
    #[test]
    fn fqize_type_expr_repairs_named_and_typevar_leaves_in_fn_sig() {
        use cranelisp_types::TypeExpr;
        let sig = "(Fn [shapes/Rectangle] (primitives/IO primitives/Int))";
        let expr = cranelisp_frontend::parse_type_expr(sig).unwrap();
        let fixed = fqize_type_expr(expr);

        let TypeExpr::FnType(params, ret) = fixed else {
            panic!("expected an Fn type expr");
        };
        // The single param `shapes/Rectangle` is now a split, qualified `Named`.
        assert_eq!(params.len(), 1);
        let TypeExpr::Named(param_ref) = &params[0] else {
            panic!("param must be a Named type ref, got {:?}", params[0]);
        };
        assert_eq!(param_ref.module, Some(ModuleFullPath::from("shapes")));
        assert_eq!(param_ref.name.as_ref(), "Rectangle");

        // The return `(primitives/IO primitives/Int)` is an Applied whose head
        // (`primitives/IO`) and arg (`primitives/Int`) are both split.
        let TypeExpr::Applied(head, args) = ret.as_ref() else {
            panic!("return must be an Applied IO type, got {ret:?}");
        };
        assert_eq!(head.module, Some(ModuleFullPath::from("primitives")));
        assert_eq!(head.name.as_ref(), "IO");
        assert_eq!(args.len(), 1);
        match &args[0] {
            TypeExpr::Named(arg_ref) => {
                assert_eq!(arg_ref.module, Some(ModuleFullPath::from("primitives")));
                assert_eq!(arg_ref.name.as_ref(), "Int");
            }
            other => panic!("IO arg must be a split Named Int, got {other:?}"),
        }
    }
}
