// `AppleLdLinker` — the macOS aarch64 (ld64) driver.
//
// The SOLE site of Apple `ld` tokens (`-arch`, `-dead_strip`, `-e _<entry>`,
// `-force_load`, `-platform_version`, `-syslibroot`, `-lSystem`). `link` and
// `describe` both render from `build_args`, so the diagnostic cannot drift from
// the executed command (the D4 fix).
//
// See design/backend/executable-generation.md §12.4 (Apple column).

use std::process::Command;

use cranelisp_types::{CranelispError, ErrorLocation, Span};

use super::{LinkRequest, Linker, describe_args, run_linker};

/// macOS arch token. Apple-ld syntax, internal to this driver (§12.2).
const APPLE_ARCH: &str = "arm64";
/// `-platform_version` triplet: (platform, min_version, sdk_version).
const APPLE_PLATFORM_TRIPLET: (&str, &str, &str) = ("macos", "14.0", "14.0");

pub(super) struct AppleLdLinker;

impl AppleLdLinker {
    pub(super) fn new() -> Self {
        AppleLdLinker
    }

    /// Build the `ld` (ld64) arg vector from the request. Byte-identical to the
    /// pre-S80-W2E `link_executable_apple_ld` rendering. `sysroot` is fetched
    /// here (the only Apple-impl-internal subprocess) so `describe` shows the
    /// real `-syslibroot` value.
    fn build_args(&self, req: &LinkRequest, sysroot: &str) -> Vec<String> {
        let (platform, min_version, sdk_version) = APPLE_PLATFORM_TRIPLET;

        let mut ld_args: Vec<String> = vec!["-arch".to_string(), APPLE_ARCH.to_string()];

        // `dead_strip` → `-dead_strip` (intent → Apple rendering).
        if req.dead_strip {
            ld_args.push("-dead_strip".to_string());
        }

        ld_args.push("-o".to_string());
        ld_args.push(req.output.to_string_lossy().to_string());
        ld_args.push("-e".to_string());
        // The Mach-O linker prepends `_` to the entry symbol name.
        ld_args.push(format!("_{}", req.entry_symbol));

        // Startup stub first.
        ld_args.push(req.startup_obj.to_string_lossy().to_string());

        // Module .o files (includes the user-main alias .o, caller-composed).
        for o_path in &req.module_objs {
            ld_args.push(o_path.to_string_lossy().to_string());
        }

        // Runtime bundle library.
        ld_args.push(format!("-L{}", req.bundle_lib.dir.to_string_lossy()));
        ld_args.push(format!("-l{}", req.bundle_lib.name));

        // Platform archives (force-loaded for #[export_name] symbols). ld64
        // force-loads the raw rlib directly — no `.o` extraction needed.
        for archive in &req.force_include {
            ld_args.push("-force_load".to_string());
            ld_args.push(archive.rlib.to_string_lossy().to_string());
        }

        // Platform version (required by modern ld).
        ld_args.push("-platform_version".to_string());
        ld_args.push(platform.to_string());
        ld_args.push(min_version.to_string());
        ld_args.push(sdk_version.to_string());

        // System library and SDK root.
        ld_args.push("-lSystem".to_string());
        ld_args.push("-syslibroot".to_string());
        ld_args.push(sysroot.to_string());

        ld_args
    }
}

impl Linker for AppleLdLinker {
    fn link(&self, req: &LinkRequest) -> Result<(), CranelispError> {
        let sysroot = get_sdk_sysroot()?;
        let args = self.build_args(req, &sysroot);
        run_linker("ld", &args)
    }

    fn describe(&self, req: &LinkRequest) -> String {
        // For the diagnostic we render from `build_args` exactly as `link` does.
        // If the SDK sysroot lookup fails, fall back to a placeholder so the
        // summary still prints the real token list — `link` will surface the
        // hard error.
        let sysroot = get_sdk_sysroot().unwrap_or_else(|_| "<sdk-sysroot>".to_string());
        let args = self.build_args(req, &sysroot);
        describe_args("ld", &args)
    }
}

/// Get the macOS SDK sysroot path via `xcrun --show-sdk-path`. Apple-only — only
/// `AppleLdLinker` calls it.
fn get_sdk_sysroot() -> Result<String, CranelispError> {
    let output = Command::new("xcrun")
        .args(["--show-sdk-path"])
        .output()
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to run xcrun: {e} (is Xcode Command Line Tools installed?)"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    if !output.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "xcrun --show-sdk-path failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}
