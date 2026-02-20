//! Platform interface: effect implementations visible to user code.
//! These functions have IO return types in the type system.

// Re-export contract types from the shared crate.
// OwnedPlatformFnDescriptor and manifest_to_descriptors are defined in
// cranelisp-platform so host and DLL share a single source of truth.
pub use cranelisp_platform::{
    manifest_to_descriptors, ABI_VERSION, HostCallbacks as HostCallbacksC,
    OwnedPlatformFnDescriptor, PlatformFn as PlatformFnC,
    PlatformManifest as PlatformManifestC,
};

// ── Platform path resolution ──────────────────────────────────────────────

/// Get the user's home directory.
fn home_dir() -> Option<std::path::PathBuf> {
    std::env::var_os("HOME")
        .or_else(|| std::env::var_os("USERPROFILE"))
        .map(std::path::PathBuf::from)
}

/// Get the Cargo-built dylib filename for a platform name.
/// Cargo names cdylib outputs as `lib<crate_name>.<ext>` on Unix,
/// `<crate_name>.dll` on Windows. Cranelisp platform crates use
/// the naming convention `cranelisp-<name>` → crate name `cranelisp_<name>`.
fn dylib_filename(platform_name: &str) -> String {
    let crate_name = format!("cranelisp_{}", platform_name.replace('-', "_"));
    if cfg!(target_os = "macos") {
        format!("lib{}.dylib", crate_name)
    } else if cfg!(target_os = "windows") {
        format!("{}.dll", crate_name)
    } else {
        format!("lib{}.so", crate_name)
    }
}

/// Resolve a platform name to a DLL path.
/// - If `name` contains '/' or '.dylib'/'.so'/'.dll', treat as filesystem path
/// - Otherwise search ./platforms/<name>.<ext> then ~/.cranelisp/platforms/<name>.<ext>
pub fn resolve_platform_path(name: &str) -> Option<std::path::PathBuf> {
    // Check if it looks like an explicit path
    if name.contains('/')
        || name.contains('\\')
        || name.ends_with(".dylib")
        || name.ends_with(".so")
        || name.ends_with(".dll")
    {
        let path = std::path::PathBuf::from(name);
        return if path.exists() { Some(path) } else { None };
    }

    let ext = if cfg!(target_os = "macos") {
        "dylib"
    } else if cfg!(target_os = "windows") {
        "dll"
    } else {
        "so"
    };

    let filename = format!("{}.{}", name, ext);

    // Search ./platforms/
    let local = std::path::PathBuf::from("platforms").join(&filename);
    if local.exists() {
        return Some(local);
    }

    // Search Cargo build output directories (development convenience)
    let lib_name = dylib_filename(name);
    let debug = std::path::PathBuf::from("target/debug").join(&lib_name);
    if debug.exists() {
        return Some(debug);
    }
    let release = std::path::PathBuf::from("target/release").join(&lib_name);
    if release.exists() {
        return Some(release);
    }

    // Search ~/.cranelisp/platforms/
    if let Some(home) = home_dir() {
        let user = home.join(".cranelisp").join("platforms").join(&filename);
        if user.exists() {
            return Some(user);
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolve_platform_path_explicit_path_nonexistent() {
        assert_eq!(resolve_platform_path("/nonexistent/foo.dylib"), None);
    }

    #[test]
    fn resolve_platform_path_explicit_path_with_slash() {
        // A path with '/' is treated as explicit — won't be found but won't panic
        assert_eq!(resolve_platform_path("./platforms/foo"), None);
    }

    #[test]
    fn resolve_platform_path_named_nonexistent() {
        // Named lookup for a platform that doesn't exist
        assert_eq!(resolve_platform_path("nonexistent_platform_xyz"), None);
    }

    #[test]
    fn abi_version_is_one() {
        assert_eq!(ABI_VERSION, 1);
    }
}
