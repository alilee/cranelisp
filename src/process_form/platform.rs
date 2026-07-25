//! Platform-form handling (S87 §1.1 optional sub-cut from `process_form.rs`).
//!
//! `handle_platform` (DLL load + §7.2 type-module pre-resolve drive + sig
//! registration) and the `layout_hash_gate` decision (platform-interface.md
//! §5.5.4). The only structural handler that touches the DLL/schema subsystem;
//! `layout_hash_gate` is extracted-for-testability (the unit test drives a
//! mismatched hash pair without dlopening a real DLL). Cross-submodule: the
//! §7.2 pre-resolve drives a dependency via `super::{fq_module_is_loaded,
//! drive_module_dep}` and returns the shared `super::BlockAction`.

use cranelisp_types::{CranelispError, ModuleFullPath, PlatformSpec};

use crate::worker::ModuleCompiler;

use super::{BlockAction, drive_module_dep, fq_module_is_loaded};

/// Outcome of the layout-hash gate (platform-interface.md §5.5.4).
///
/// Separating the decision from its enaction (`eprintln!` / `return Err`) makes
/// the gate's three branches unit-testable without capturing stderr or
/// dlopening a real DLL: a matching pair → `Accept`, a mismatched pair in the
/// REPL → `WarnAndLoad` (the regeneration bootstrap), a mismatched pair in
/// `--run`/`--link` → `Refuse` carrying `PlatformError::LayoutHashMismatch`.
pub(crate) enum LayoutHashGate {
    /// Hashes match (or the host hash is empty — first-build/absent tolerated).
    Accept,
    /// Mismatch in the REPL: warn and load anyway (the only place the schema
    /// can be regenerated). Carries the warning text.
    WarnAndLoad(String),
    /// Mismatch in `--run`/`--link`: hard refusal carrying both hashes.
    Refuse(CranelispError),
}

/// Decide the layout-hash gate outcome from a (DLL hash, host-regenerated hash)
/// pair (platform-interface.md §5.5.4). Extracted from `handle_platform` as the
/// smallest pure owner of the compare + REPL/`--run` branch — the surrounding
/// `handle_platform` needs a full `ModuleCompiler` (and dlopens the platform),
/// so the dual-gate decision cannot otherwise be driven with a mismatched pair.
/// Minimum mechanism, no behaviour change: the load path and the unit test call
/// the same decision.
pub(crate) fn layout_hash_gate(
    dll_hash: &str,
    host_hash: &str,
    platform_name: &str,
    is_repl: bool,
    span: cranelisp_types::Span,
) -> LayoutHashGate {
    // A matching pair, or an empty host hash (the host regenerated nothing —
    // first-build/absent, §5.5.4), accepts.
    if host_hash == dll_hash || host_hash.is_empty() {
        return LayoutHashGate::Accept;
    }
    if is_repl {
        LayoutHashGate::WarnAndLoad(format!(
            "warning: platform '{platform_name}' layout hash mismatch (DLL embedded \
             {dll_hash}, host regenerated {host_hash}); loading anyway — run \
             `/platform-schema {platform_name}` and rebuild the platform to refresh \
             its embedded schema."
        ))
    } else {
        LayoutHashGate::Refuse(CranelispError::Platform(
            cranelisp_types::PlatformError::LayoutHashMismatch {
                dll: std::path::PathBuf::from(format!("platform.{platform_name}")),
                platform: platform_name.to_string(),
                expected: host_hash.to_string(),
                found: dll_hash.to_string(),
                location: cranelisp_types::ErrorLocation::from_span(span),
            },
        ))
    }
}

/// Handle platform forms: load DLL, pre-resolve associated type modules, and
/// register type signatures.
///
/// Platform loading is NOT a cross-module blocking operation for the DLL load
/// itself (it is synchronous). But a platform whose function signatures name
/// types from a user `.cl` type-module (`shapes/Rectangle`) MUST have those
/// modules resolved + registered BEFORE its sigs are checked
/// (platform-interface.md §7.2 "q-assoc-discovery (c); BEFORE sigs"). An
/// unresolved FQ sig type-ref surfaces as a `ModuleError`, NOT a
/// `ResolutionGap`, so the ordinary FQ-autoload retry (FIXME 0268) never fires
/// for platform sigs — this function closes that gap by driving each referenced
/// type module via the same dependency mechanism as `import`, blocking the
/// referencing cluster and retrying from the top once the dep is live.
///
/// Returns `BlockAction::Block { dep }` when a referenced type module is not yet
/// loaded (the cluster retries; this fn re-runs once the dep is live, at which
/// point all sigs resolve and it proceeds to register). Returns
/// `BlockAction::Continue` once every referenced type module is present and the
/// platform is fully registered.
///
/// Platform declarations in non-entry modules (submodules) are silently
/// ignored per spec §10.9.1 — only the entry module may load platforms.
pub(super) fn handle_platform(
    ctx: &mut ModuleCompiler,
    module: &ModuleFullPath,
    spec: &PlatformSpec,
) -> Result<BlockAction, CranelispError> {
    // Submodules (paths containing '.') cannot load platforms.
    if module.as_ref().contains('.') {
        return Ok(BlockAction::Continue);
    }

    // Load + validate the DLL (without registering sigs yet) so we can read its
    // descriptor sig strings to discover the associated type modules.
    let platform = crate::platform::load_platform_checked(
        &spec.name,
        ctx.project_root,
        ctx.lib_dirs,
        ctx.platform_dirs,
        spec.span,
    )?;

    // §7.2 pre-resolve: for each EXTERNAL type module a sig references
    // (`shapes` from `shapes/Rectangle`), drive it as a dependency BEFORE the
    // sig-check loop runs. If any is not yet loaded, block + retry-from-top —
    // the DLL handle drops at this return; the next pass re-dlopens (OS-cached)
    // and finds the now-loaded module, so the sigs resolve.
    for dep in crate::platform::referenced_sig_modules(&platform.descriptors) {
        if !fq_module_is_loaded(ctx, &dep) {
            drive_module_dep(ctx, module, &dep, spec.span)?;
            return Ok(BlockAction::Block { dep_module: dep });
        }
    }

    // All referenced type modules are live — register the platform's sigs (GOT
    // wrap in place + FQ-resolved schemes + got_slot = manifest index).
    crate::platform::register_platform_in_tc(ctx.symbol_tables, ctx.module_aliases, &platform)?;

    // The platform module's `SymbolTable` now wraps the DLL's exported GOT in
    // place (`register_platform_in_tc`, platform-interface.md §6.4) and carries
    // `got_slot = manifest index` per entry — the GOT-indirect dispatch arm in
    // backend (`apply.rs`) reaches the platform fns identically to any user
    // module. No per-slot allocation / fn-ptr store is needed here anymore (the
    // DLL owns + populated the slab); the old G8 slot-allocation loop is gone.
    let module_path = ModuleFullPath::from(format!("platform.{}", platform.name));

    // Layout-hash gate (platform-interface.md §5.5.4, §6.4): regenerate the
    // schema from the live tables (the same backend generator the DLL ran at
    // /platform-schema time) and compare its canonical hash to the DLL's
    // exported `__cranelisp_layout_hash_<name>`. REPL warns-and-loads (the
    // regeneration bootstrap, §5.5.1); `--run` (non-REPL) hard-refuses. A
    // platform that declared no schema (scalar-only, no ADTs) exports no hash —
    // tolerated (first-build/absent, §5.5.4).
    if let Some(dll_hash) = &platform.layout_hash {
        let roots = ctx
            .symbol_tables
            .get(&module_path)
            .map(|t| cranelisp_backend::schema::platform_effect_roots(&t))
            .unwrap_or_default();
        let host_hash = cranelisp_backend::schema::compute_layout_hash(ctx.symbol_tables, &roots);
        // is_repl: the explicit run-mode signal (D1 ruling §4). REPL warns-and-
        // loads on layout-hash drift (the regeneration bootstrap, §5.5.1);
        // `--run`/`--link` hard-refuse. Read from `SharedState.run_mode` — the
        // single source of truth — replacing the former `introspection.is_some()`
        // proxy (introspection became always-`Some` under S78, conflating a REPL
        // facility with the batch discriminator). Absent shared state (unit-test
        // paths that never load a real platform) defaults to non-REPL = refuse.
        let is_repl = ctx
            .shared_state
            .map(|s| s.run_mode.is_repl())
            .unwrap_or(false);
        match layout_hash_gate(dll_hash, &host_hash, &platform.name, is_repl, spec.span) {
            LayoutHashGate::Accept => {}
            LayoutHashGate::WarnAndLoad(msg) => eprintln!("{msg}"),
            LayoutHashGate::Refuse(err) => return Err(err),
        }
    }

    // Retain the DLL handle on the session's `kept_dlls` pool so that the
    // GOT pointers remain valid for the session lifetime. Without this
    // push, the `LoadedPlatform` would drop at the end of this function,
    // `libloading::Library::drop` would `dlclose` the DLL, and every
    // GOT entry would dangle.
    if let Some(shared) = ctx.shared_state {
        shared
            .kept_dlls
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push(platform);
    } else {
        // REPL path without a shared_state: leak the DLL handle so its
        // pointers remain valid for the process lifetime. This matches the
        // pre-G8 comment that "Platform DLLs are leaked (kept alive for
        // process lifetime)". Dropping `platform` here would `dlclose` the
        // DLL and dangle every GOT entry.
        std::mem::forget(platform);
    }
    Ok(BlockAction::Continue)
}
