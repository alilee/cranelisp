// The `Linker` abstraction — intent in, platform tokens out (S80 Wave 2E).
//
// `--link` linking is expressed as a platform-neutral `LinkRequest` (what to
// link and why) and rendered to toolchain-specific args by a `Linker` impl.
// Each impl is the SOLE site where its platform's link tokens (`-force_load`,
// `--whole-archive`, `-arch`, `-dead_strip`, …) appear — including in the
// diagnostic, which renders the real command via the SAME arg-building path it
// executes. This is the structural fix for bug D4 (Principle 18 — enforce
// invariants structurally; Principle 7 — single source of truth): the
// `; Linking: …` summary literally cannot show a flag the real link did not use.
//
// See design/backend/executable-generation.md §12 for the contract.
//
// Owned by /int (binary-crate link orchestration).

mod apple;
mod gnu;

use std::path::{Path, PathBuf};
use std::process::Command;

use cranelisp_types::{CranelispError, ErrorLocation, Span};

/// The bundle library to link against (the runtime `.a`): its directory and its
/// link name (the `lib`-stripped stem — e.g. `cranelisp_exe_bundle`).
pub(crate) struct BundleLib {
    pub(crate) dir: PathBuf,
    pub(crate) name: String,
}

/// A platform static archive whose `#[export_name]` symbols (GOT / manifest /
/// layout-hash) are referenced BY NAME at runtime, not by relocation, so a
/// normal link would dead-strip them. The linker MUST force every object of this
/// archive into the output. On GNU this is the *raw* `.rlib`; the GNU driver is
/// responsible for extracting its `.o` members (§12.5).
pub(crate) struct ForceIncludeArchive {
    pub(crate) rlib: PathBuf,
}

/// A native-link request expressed as intent. No platform/toolchain tokens —
/// those are driver renderings of these fields (§12.2).
pub(crate) struct LinkRequest {
    /// The startup-stub object (the executable entry: macOS `start`, Linux C `main`).
    pub(crate) startup_obj: PathBuf,
    /// Compiled module objects, including the user-main alias `.o` (caller-composed).
    pub(crate) module_objs: Vec<PathBuf>,
    /// The runtime bundle archive.
    pub(crate) bundle_lib: BundleLib,
    /// Platform archives whose export-name symbols must survive dead-strip.
    /// Empty for non-platform programs.
    pub(crate) force_include: Vec<ForceIncludeArchive>,
    /// The executable entry symbol the stub exports. macOS `"start"` (the driver
    /// adds the `-e _start` form); Linux `"main"` (crt's default entry — the
    /// driver omits `-e`). Carried as intent; the driver decides the flag. The
    /// macOS Mach-O underscore prefix is a driver rendering, NOT carried here.
    pub(crate) entry_symbol: String,
    /// Whether to dead-strip unused symbols. macOS `-dead_strip`; GNU
    /// `-Wl,--gc-sections`.
    pub(crate) dead_strip: bool,
    /// Output executable path.
    pub(crate) output: PathBuf,
}

/// A native linker driver. Each impl is the SOLE place its platform's link
/// tokens appear. `link` executes; `describe` renders the same command for
/// diagnostics — both flow through the same arg-building path so the printed
/// command cannot drift from the executed one (the D4 fix, §12.3).
pub(crate) trait Linker {
    /// Build the toolchain arg vector from the request and invoke the linker.
    fn link(&self, req: &LinkRequest) -> Result<(), CranelispError>;

    /// Render the command this impl WOULD run for `req`, as a human-readable
    /// string, for the `; Linking: …` diagnostic. Produced from the same
    /// arg-building path `link` uses — never an independent re-spelling.
    fn describe(&self, req: &LinkRequest) -> String;
}

/// The native linker driver for the current host (replaces the old
/// `LinkerConfig::for_host`). macOS aarch64 → Apple `ld`; Linux aarch64 → `cc`
/// driver (§12.6).
pub(crate) fn for_host() -> Result<Box<dyn Linker>, CranelispError> {
    match (cfg!(target_arch = "aarch64"), std::env::consts::OS) {
        (true, "macos") => Ok(Box::new(apple::AppleLdLinker::new())),
        (true, "linux") => Ok(Box::new(gnu::GnuCcLinker::new())),
        _ => Err(CranelispError::CodegenError {
            message: "standalone executable generation is only supported on \
                      aarch64 macOS and aarch64 Linux"
                .to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

/// The startup-stub export symbol and the user-main alias symbol for the host
/// (§11.3). Read by the call site (`session_v4.rs`) so the stub's import of user
/// main and the alias's export use the host-correct names.
///
/// Returns `(stub_entry_symbol, user_main_symbol)`.
pub(crate) fn host_entry_symbols() -> Result<(&'static str, &'static str), CranelispError> {
    match (cfg!(target_arch = "aarch64"), std::env::consts::OS) {
        // macOS keeps its custom crt-bypassing entry (`start` / `main`, Apple `ld`).
        (true, "macos") => Ok(("start", "main")),
        // Linux routes through crt: the stub IS C `main`, so the user-main alias
        // is renamed `cranelisp_user_main` to avoid colliding with the C `main`.
        (true, "linux") => Ok(("main", "cranelisp_user_main")),
        _ => Err(CranelispError::CodegenError {
            message: "standalone executable generation is only supported on \
                      aarch64 macOS and aarch64 Linux"
                .to_string(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

/// Spawn the linker driver and surface a non-zero exit as a `CodegenError`.
/// Shared by both impls (the program + args are the impl's own; the spawn is
/// platform-neutral).
pub(super) fn run_linker(program: &str, args: &[String]) -> Result<(), CranelispError> {
    let output =
        Command::new(program)
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

/// Render a `; Linking: <command>` diagnostic line by trimming each arg to its
/// file name where it is a path. Shared rendering helper for the impls'
/// `describe` so both elide absolute-path noise identically; every *token* still
/// comes from the impl's own `build_args`.
pub(super) fn describe_args(program: &str, args: &[String]) -> String {
    let parts: Vec<String> = args.iter().map(|a| short_arg(a)).collect();
    format!("; Linking: {program} {}", parts.join(" "))
}

/// Shorten a single arg for the diagnostic: bare path args and the value half of
/// flag-prefixed paths (`-L<dir>`, `-l<name>` are left whole; an absolute path
/// is reduced to its file name). Non-path tokens pass through unchanged.
fn short_arg(arg: &str) -> String {
    // Leave flag tokens whole; only shorten bare path-looking args.
    if arg.starts_with('-') {
        return arg.to_string();
    }
    if arg.contains('/') {
        return Path::new(arg)
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| arg.to_string());
    }
    arg.to_string()
}
