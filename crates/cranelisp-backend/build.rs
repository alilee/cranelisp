// Build script — emits CRANELISP_BUILD_ID into the backend crate's env.
//
// Sprint 60 Workstream C: the cache envelope carries a compile-time build-id
// alongside `CACHE_SCHEMA_VERSION` so that a `cargo build` that rewrites the
// compiler — without anyone remembering to bump `CACHE_SCHEMA_VERSION` —
// still invalidates stale caches. This is an **additional** invalidation
// trigger; the Decision 34 manual-bump discipline on serialised-shape changes
// is unchanged.
//
// Format: `<pkg_version>+<git_sha>` e.g. `0.1.0+3b2df720fe63`. If git is
// absent (source tarball, sandboxed build), the sha falls back to `unknown`
// and the build-id becomes `<pkg_version>+unknown` — still distinct from
// pre-Sprint-60 caches (empty field), still stable within one checkout, and
// varies across pkg-version bumps.

use std::process::Command;

fn main() {
    let pkg_version = env!("CARGO_PKG_VERSION");

    let git_sha = Command::new("git")
        .args(["rev-parse", "--short=12", "HEAD"])
        .output()
        .ok()
        .filter(|out| out.status.success())
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "unknown".to_string());

    println!("cargo:rustc-env=CRANELISP_BUILD_ID={pkg_version}+{git_sha}");

    // Re-run when HEAD moves or the index is restamped. Missing files are
    // tolerated silently by cargo; `build.rs` itself is always tracked.
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../../.git/HEAD");
    println!("cargo:rerun-if-changed=../../.git/index");
}
