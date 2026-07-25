// `GnuCcLinker` — the Linux aarch64 (`cc`/gcc driver) linker.
//
// The SOLE site of GNU link tokens (`-Wl,--whole-archive`, `-Wl,--gc-sections`,
// the `-lpthread -ldl -lm` Rust-std externs). `link` and `describe` both render
// from `build_args`, so the diagnostic cannot drift from the executed command.
//
// The GNU-specific `.rlib` object-extraction (§12.5) and the before-bundle
// link-order constraint live here — they are GNU's rendering of the request's
// platform-neutral `force_include` intent, meaningless to the caller or Apple.
//
// See design/backend/executable-generation.md §12.4 (GNU column) + §12.5.

use std::path::{Path, PathBuf};
use std::process::Command;

use cranelisp_types::{CranelispError, ErrorLocation, Span};

use super::{LinkRequest, Linker, describe_args, run_linker};

pub(super) struct GnuCcLinker;

impl GnuCcLinker {
    pub(super) fn new() -> Self {
        GnuCcLinker
    }

    /// Build the `cc`-driver arg vector from the request, extracting platform
    /// `.rlib` object members as the GNU rendering of `force_include`. No `-e`
    /// (crt's `_start` is the default entry; our `main` is the C entry), no
    /// `-syslibroot`, no `-platform_version`.
    fn build_args(&self, req: &LinkRequest) -> Result<Vec<String>, CranelispError> {
        let mut cc_args: Vec<String> =
            vec!["-o".to_string(), req.output.to_string_lossy().to_string()];

        // Startup stub (the C `main`) first.
        cc_args.push(req.startup_obj.to_string_lossy().to_string());

        // Module .o files (includes the user-main alias .o, caller-composed).
        for o_path in &req.module_objs {
            cc_args.push(o_path.to_string_lossy().to_string());
        }

        // Platform statics — GNU `--whole-archive` is the equivalent of macOS
        // `-force_load`, pulling in the platform's `#[export_name]` GOT/manifest/
        // layout-hash symbols. Empty for non-platform programs.
        //
        // A real Rust `.rlib` is an `ar` archive carrying a `lib.rmeta`
        // (+ `lib.rmeta-link`) metadata member that GNU `ld`/mold reject under
        // `--whole-archive` ("file format not recognized"). So instead of
        // whole-archiving the raw `.rlib`, we extract its object members into a
        // deterministic per-platform cache dir and whole-archive only those `.o`s.
        //
        // ORDER: the whole-archive platform objects MUST precede the runtime
        // bundle `-l`. A platform object references `cranelisp_platform::adt::*`
        // (and other workspace symbols) that live in the bundle; GNU `ld`
        // resolves a static archive (`.a`) only against symbols left-undefined by
        // inputs seen SO FAR. If the bundle came first, the later platform
        // objects' fresh undefined refs would never be satisfied. Placed before
        // the bundle, the platform's undefined refs are open when it is scanned.
        if !req.force_include.is_empty() {
            // The startup `.o` lives in the cache dir (session_v4.rs writes both
            // there); use its parent as the stable extraction-root so the
            // extracted `.o`s sit beside the other link inputs and are debuggable.
            let cache_dir = req.startup_obj.parent().unwrap_or_else(|| Path::new("."));
            cc_args.push("-Wl,--whole-archive".to_string());
            for archive in &req.force_include {
                let objects = extract_rlib_objects(&archive.rlib, cache_dir)?;
                for obj in objects {
                    cc_args.push(obj.to_string_lossy().to_string());
                }
            }
            cc_args.push("-Wl,--no-whole-archive".to_string());
        }

        // Runtime bundle library (embeds Rust std + the workspace platform crate).
        cc_args.push(format!("-L{}", req.bundle_lib.dir.to_string_lossy()));
        cc_args.push(format!("-l{}", req.bundle_lib.name));

        // Rust-std external deps that must be satisfied at final link. The driver
        // supplies `-lc`/`-lgcc_s`; std additionally needs these (confirmed
        // empirically — design §11.4).
        cc_args.push("-lpthread".to_string());
        cc_args.push("-ldl".to_string());
        cc_args.push("-lm".to_string());

        // `dead_strip` → GNU `-Wl,--gc-sections` is intentionally a NO-OP here,
        // matching today's behaviour (design §11.4 / §12.4 GNU row: "currently
        // omitted — optional for correctness"). Enabling `--gc-sections` would
        // garbage-collect the std/platform sections the whole-archived platform
        // `.o`s reference by name, producing spurious `undefined reference`s. The
        // `req.dead_strip` intent is honoured only by `AppleLdLinker`; the GNU
        // driver leaves the link complete (the §11.4 "basic path is green without
        // it" note). Reads `req.dead_strip` would-be branch deliberately absent.
        let _ = req.dead_strip;

        Ok(cc_args)
    }
}

impl Linker for GnuCcLinker {
    fn link(&self, req: &LinkRequest) -> Result<(), CranelispError> {
        let args = self.build_args(req)?;
        run_linker("cc", &args)
    }

    fn describe(&self, req: &LinkRequest) -> String {
        // Render from the same arg-builder `link` uses. Extraction is part of
        // arg-building; if it fails here the placeholder keeps the summary
        // printable — `link` surfaces the hard error.
        match self.build_args(req) {
            Ok(args) => describe_args("cc", &args),
            Err(_) => "; Linking: cc <args unavailable: rlib extraction failed>".to_string(),
        }
    }
}

/// Extract the object members of a Rust `.rlib` so they can be whole-archived
/// individually on Linux (§12.5, option 1). GNU-only.
///
/// A Rust `.rlib` is a GNU `ar` archive of object members (`*.rcgu.o`) PLUS a
/// `lib.rmeta` metadata member (and a `lib.rmeta-link` sidecar). GNU `ld`/mold
/// under `--whole-archive` try to link EVERY member as an object and choke on
/// the rmeta members ("file format not recognized") — Apple `ld64` tolerates
/// this, GNU does not. So we list the archive (`ar t`), keep only the object
/// members (names ending in `.o`, which excludes `lib.rmeta` /
/// `lib.rmeta-link`), and extract just those into a deterministic per-rlib dir
/// under the cache (`<cache>/__plat_<stem>/`), returning the extracted `.o`
/// paths for the caller to whole-archive.
///
/// The extraction dir is deterministic (not a random temp) so paths stay stable
/// across builds and are inspectable when a link fails. Shells out to the system
/// `ar` (already required on the Linux toolchain) rather than adding an
/// `ar`/`object` crate dependency.
fn extract_rlib_objects(
    rlib_path: &Path,
    cache_dir: &Path,
) -> Result<Vec<PathBuf>, CranelispError> {
    let stem = rlib_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("platform");
    let out_dir = cache_dir.join(format!("__plat_{stem}"));

    // Fresh extraction each link: clear any stale objects so a rebuilt rlib does
    // not leave orphaned members behind in the deterministic dir.
    if out_dir.exists() {
        std::fs::remove_dir_all(&out_dir).map_err(|e| CranelispError::CodegenError {
            message: format!(
                "failed to clear platform-object dir {}: {e}",
                out_dir.display()
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    }
    std::fs::create_dir_all(&out_dir).map_err(|e| CranelispError::CodegenError {
        message: format!(
            "failed to create platform-object dir {}: {e}",
            out_dir.display()
        ),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })?;

    // List the archive members. `ar t` prints one member name per line.
    let listing = Command::new("ar")
        .arg("t")
        .arg(rlib_path)
        .output()
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to run `ar t {}`: {e}", rlib_path.display()),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    if !listing.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "`ar t {}` failed:\n{}",
                rlib_path.display(),
                String::from_utf8_lossy(&listing.stderr)
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    // Keep only object members. Rust rlib objects end in `.o` (the `*.rcgu.o`
    // codegen units); `lib.rmeta` / `lib.rmeta-link` do not end in `.o` and are
    // dropped — they are the members GNU `--whole-archive` rejects.
    let object_members: Vec<String> = String::from_utf8_lossy(&listing.stdout)
        .lines()
        .map(str::trim)
        .filter(|m| !m.is_empty() && m.ends_with(".o"))
        .map(str::to_string)
        .collect();

    if object_members.is_empty() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "platform rlib {} contains no object members to whole-archive",
                rlib_path.display()
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    // Extract just the object members into the per-rlib dir. GNU `ar` supports
    // `--output=DIR` to place extracted members somewhere other than cwd.
    let extract = Command::new("ar")
        .arg(format!("--output={}", out_dir.display()))
        .arg("x")
        .arg(rlib_path)
        .args(&object_members)
        .output()
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to run `ar x {}`: {e}", rlib_path.display()),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    if !extract.status.success() {
        return Err(CranelispError::CodegenError {
            message: format!(
                "`ar x {}` failed:\n{}",
                rlib_path.display(),
                String::from_utf8_lossy(&extract.stderr)
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    Ok(object_members
        .into_iter()
        .map(|m| out_dir.join(m))
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: design/backend/executable-generation.md §11.5 — Phase 2 rlib object
    // extraction: only object members (`*.o`) are extracted; the rmeta family
    // (`lib.rmeta` / `lib.rmeta-link`) is skipped, and the extracted `.o`s land
    // in a deterministic `__plat_<stem>/` dir under the supplied cache dir.
    #[test]
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    fn extract_rlib_objects_keeps_only_objects() {
        let dir = tempfile::tempdir().unwrap();
        let obj = dir.path().join("unit.o");
        std::fs::write(&obj, b"\x7fELF-not-really-but-ends-in-o").unwrap();
        let rmeta = dir.path().join("lib.rmeta");
        std::fs::write(&rmeta, b"rust-metadata").unwrap();
        let rlib = dir.path().join("libfake_platform.rlib");
        let status = Command::new("ar")
            .arg("rcs")
            .arg(&rlib)
            .arg(&obj)
            .arg(&rmeta)
            .status()
            .unwrap();
        assert!(status.success(), "ar rcs failed to build fixture archive");

        let cache = dir.path().join("cache");
        std::fs::create_dir_all(&cache).unwrap();
        let objects = extract_rlib_objects(&rlib, &cache).unwrap();

        assert_eq!(objects.len(), 1, "extracted: {objects:?}");
        let extracted = &objects[0];
        assert_eq!(extracted.file_name().unwrap(), "unit.o");
        assert!(extracted.exists(), "extracted .o must be on disk");
        assert!(extracted.starts_with(cache.join("__plat_libfake_platform")));
        assert!(
            !cache
                .join("__plat_libfake_platform")
                .join("lib.rmeta")
                .exists()
        );
    }
}
