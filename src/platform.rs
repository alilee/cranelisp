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
/// 2. Look up the per-platform-namespaced `cranelisp_platform_manifest_<name>`
///    entry point (platform-interface.md §5.5.5 / §6.7 — the manifest export is
///    suffixed by the platform name like the GOT and layout-hash exports, so two
///    platforms can link into one binary; DEF-5). The symbol name is computed
///    from `platform_name` via `cranelisp_platform::platform_manifest_symbol` —
///    the shared emit/consume helper, never an inline `format!`. The name is
///    known here from the `(platform "<name>")` declaration (the caller's lookup
///    key), before the manifest is read.
/// 3. Call it with a `HostCallbacks` containing the runtime allocator.
/// 4. Validate ABI version.
/// 5. Convert C-ABI manifest to safe Rust types.
///
/// Returns a `LoadedPlatform` that must remain alive for the process lifetime.
pub fn load_platform_dll(
    platform_name: &str,
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

    // Steps 2–5: obtain `(name, version, descriptors)` from the platform's
    // manifest. Calling a manifest fn ALSO inits the host context (allocator)
    // and populates the DLL's exported GOT slab (manifest order IS GOT slot
    // order, §5.1), which we dlsym in step 6.
    //
    // `alloc_with_tag` is wired to the real intrinsic (S76 W3, FIXME 0229):
    // `cranelisp_alloc_with_tag` allocates a tagged heap ADT over
    // `alloc::alloc_with_rc`. The `validate_schema` callback is gone (FIXME
    // 0288): schema validation is superseded by the layout-hash gate (§5.5.4).
    let callbacks = HostCallbacks {
        alloc: cranelisp_intrinsics::heap_alloc_payload,
        alloc_with_tag: cranelisp_intrinsics::alloc::cranelisp_alloc_with_tag,
    };

    // v7 channel (FIXME 0457, `platform-interface.md` §6.8): a concurrency-built
    // host probes the v7 `cranelisp_concurrent_manifest` export FIRST. A
    // poll-shape platform (e.g. `async-demo`) exposes its effects ONLY through
    // this separate manifest type + symbol; on a hit we lift them via
    // `concurrent_manifest_to_descriptors` (which carries each effect's
    // `ConcurrencyDescriptor`). The default (non-concurrency) host compiles this
    // probe out entirely, so v6 platforms + the default host stay byte-identical.
    #[cfg(feature = "concurrency")]
    let concurrent: Option<(String, String, Vec<OwnedPlatformFnDescriptor>)> = {
        let probe: Result<
            libloading::Symbol<
                unsafe extern "C" fn(
                    *const HostCallbacks,
                )
                    -> cranelisp_platform::ConcurrentPlatformManifest,
            >,
            _,
        > = unsafe { library.get(b"cranelisp_concurrent_manifest") };
        match probe {
            Ok(cm_fn) => {
                let manifest = unsafe { cm_fn(&callbacks) };
                check_abi_version(manifest.abi_version, dll_path, location())?;
                let triple = unsafe {
                    cranelisp_platform::concurrent_manifest_to_descriptors(&manifest).map_err(
                        |e| match e {
                            cranelisp_types::PlatformError::LoadFailed { cause, .. } => {
                                CranelispError::Platform(
                                    cranelisp_types::PlatformError::LoadFailed {
                                        dll: dll_path.to_path_buf(),
                                        cause,
                                        location: location(),
                                    },
                                )
                            }
                            other => CranelispError::Platform(other),
                        },
                    )?
                };
                Some(triple)
            }
            // No v7 export ⇒ a v6 blocking platform; fall through.
            Err(_) => None,
        }
    };
    #[cfg(not(feature = "concurrency"))]
    let concurrent: Option<(String, String, Vec<OwnedPlatformFnDescriptor>)> = None;

    let (name, version, descriptors) = match concurrent {
        Some(triple) => triple,
        None => {
            // v6 path: the per-platform-namespaced manifest fn
            // (`cranelisp_platform_manifest_<name>`, §5.5.5 / §6.7 / DEF-5). The
            // name is known here from the declaration, computed via the shared
            // helper (never an inline `format!`).
            let manifest_sym_name =
                cranelisp_platform::platform_manifest_symbol(platform_name);
            type ManifestFn = unsafe extern "C" fn(*const HostCallbacks) -> PlatformManifest;
            let manifest_fn: libloading::Symbol<ManifestFn> = unsafe {
                library.get(manifest_sym_name.as_bytes()).map_err(|_e| {
                    CranelispError::Platform(cranelisp_types::PlatformError::ManifestNotFound {
                        dll: dll_path.to_path_buf(),
                        location: location(),
                    })
                })?
            };
            let manifest = unsafe { manifest_fn(&callbacks) };
            check_abi_version(manifest.abi_version, dll_path, location())?;
            // `manifest_to_descriptors` constructs `PlatformError::LoadFailed`
            // with `ErrorLocation::unknown()`; rewrite both at this call site so
            // the user sees the `(platform "name")` form span.
            unsafe {
                cranelisp_platform::manifest_to_descriptors(&manifest).map_err(|e| match e {
                    cranelisp_types::PlatformError::LoadFailed { cause, .. } => {
                        CranelispError::Platform(cranelisp_types::PlatformError::LoadFailed {
                            dll: dll_path.to_path_buf(),
                            cause,
                            location: location(),
                        })
                    }
                    // Defensive: forward any non-LoadFailed variant.
                    other => CranelispError::Platform(other),
                })?
            }
        }
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

        // Insert directly into the module's symbol table with the GOT slot =
        // manifest index (§5.3). The slot now rides on the `PlatformEffect`
        // variant (S83 reshape, FIXME 0358 — PlatformEffect IS GOT-callable);
        // the GOT-indirect dispatch arm in backend (`apply.rs`) activates on
        // the variant's `got_slot`.
        if let Some(mut table) = symbol_tables.get_mut(&module_path) {
            // FIXME 0457 (S94): the poll-shape dispatch axis. Ungated (v6 /
            // default host) ⇒ always `false` (byte-identical blocking). The
            // concurrency host lifts it from the v7 descriptor:
            // `concurrency.blocking == 0` ⇒ a poll-shape async leaf ⇒ the
            // backend's poll-construction arm.
            #[cfg(feature = "concurrency")]
            let poll_shape = desc.concurrency.map_or(false, |c| c.blocking == 0);
            #[cfg(not(feature = "concurrency"))]
            let poll_shape = false;

            let mut builder = ModuleEntry::def(
                scheme,
                DefKind::PlatformEffect {
                    scheduling_class: desc.scheduling_class,
                    poll_shape,
                    got_slot: slot,
                },
            )
            .visibility(Visibility::Public)
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

/// Resolve a platform's DLL path, load + validate it, and confirm the manifest
/// name matches the declared name — but do NOT register the sigs in the symbol
/// tables.
///
/// This is the load half of `load_and_register_platform`, split out so the
/// worker can interpose the §7.2 "resolve + compile associated `.cl` type
/// module(s) BEFORE sigs" step between loading the DLL (which surfaces the
/// descriptor sig strings naming `shapes/Rectangle` etc.) and registering the
/// sigs (which resolve those FQ type refs against the now-loaded type modules).
pub fn load_platform_checked(
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
    let platform = load_platform_dll(platform_name, &dll_path, span)?;

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

    Ok(platform)
}

/// The set of EXTERNAL `.cl` type-modules a platform's function signatures
/// reference (platform-interface.md §7.2 "q-assoc-discovery").
///
/// A platform sig like `(Fn [shapes/Rectangle] (primitives/IO primitives/Int))`
/// references the user type-module `shapes` (via `shapes/Rectangle`). Such a
/// module must be resolved + registered BEFORE the sig is checked, because the
/// sig-check resolves `shapes/Rectangle` against module `shapes`'s symbol table
/// — and an unresolved FQ sig type-ref surfaces as a `ModuleError`, NOT a
/// `ResolutionGap`, so the ordinary FQ-autoload retry (FIXME 0268) never fires
/// for platform sigs. This pre-resolve closes that gap.
///
/// Modules that are always synthetically present are excluded: `primitives`
/// (intrinsic types + `IO`), `macros`, and any already-loaded module the caller
/// filters out. Returns the distinct external module paths in first-seen order
/// (deterministic, so the worker drives a stable dep at a time).
pub fn referenced_sig_modules(descriptors: &[OwnedPlatformFnDescriptor]) -> Vec<ModuleFullPath> {
    let mut seen: Vec<ModuleFullPath> = Vec::new();
    for desc in descriptors {
        // A sig that fails to parse here is not our concern — the sig-check
        // loop reports the parse error with the proper diagnostic. We only
        // harvest the module prefixes from sigs that DO parse.
        let Ok(expr) = cranelisp_frontend::parse_type_expr(&desc.type_sig) else {
            continue;
        };
        let expr = fqize_type_expr(expr);
        collect_type_expr_modules(&expr, &mut seen);
    }
    seen
}

/// Walk a (already `fqize`d) `TypeExpr`, pushing every distinct external module
/// prefix carried on a qualified `Named`/`Applied` leaf into `acc`. The
/// always-synthetic `primitives` / `macros` modules are skipped — they are
/// mounted at session init and never need a `.cl` file load.
fn collect_type_expr_modules(expr: &cranelisp_types::TypeExpr, acc: &mut Vec<ModuleFullPath>) {
    use cranelisp_types::TypeExpr;
    let push_module = |m: &Option<ModuleFullPath>, acc: &mut Vec<ModuleFullPath>| {
        if let Some(module) = m {
            let s = module.as_ref();
            if s != "primitives" && s != "macros" && !acc.iter().any(|seen| seen == module) {
                acc.push(module.clone());
            }
        }
    };
    match expr {
        TypeExpr::Named(tref) => push_module(&tref.module, acc),
        TypeExpr::Applied(head, args) => {
            push_module(&head.module, acc);
            for arg in args {
                collect_type_expr_modules(arg, acc);
            }
        }
        TypeExpr::FnType(params, ret) => {
            for p in params {
                collect_type_expr_modules(p, acc);
            }
            collect_type_expr_modules(ret, acc);
        }
        TypeExpr::TypeVar(_) => {}
        _ => {}
    }
}

/// Full platform loading pipeline: resolve path, load DLL, validate manifest,
/// register in the host symbol tables (GOT wrapped in place, got_slot = manifest
/// index, FQ sigs — no injected imports, no jit_name registration).
///
/// Returns the loaded platform; the caller MUST keep it alive (retain on
/// `SharedState::kept_dlls`) so the wrapped GOT slab + fn pointers stay valid.
///
/// NOTE: this composition does NOT perform the §7.2 associated-type-module
/// pre-resolve — it is retained for callers (unit tests) whose platforms have
/// scalar-only sigs (`stdio`). The worker (`handle_platform`) uses
/// `load_platform_checked` + `referenced_sig_modules` + `register_platform_in_tc`
/// so it can drive the type-module deps between load and register.
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
    let platform = load_platform_checked(
        platform_name, project_root, lib_dirs, platform_dirs, span,
    )?;

    // Register in the host symbol tables (GOT wrap + FQ sigs).
    register_platform_in_tc(symbol_tables, module_aliases, &platform)?;

    Ok(platform)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
