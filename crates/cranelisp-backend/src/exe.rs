//! Startup-stub types for standalone executables (`--link` mode).
//!
//! **Startup-`.o` emission lives in `int`, not here.** The `--link` startup
//! object (the `.o` defining the `start` entry symbol that inits platforms,
//! calls `main`, runs the IO trampoline, and `exit`s) is produced by
//! `int`'s `src/exe.rs::generate_startup_object` (called from
//! `session_v4/lifecycle.rs`) — the production copy, per BC §3 invariant 7
//! ("the `--link` `_main`/`start` alias is int's job, not backend's"; the
//! relocation to int landed at S76 §4.4). The orphaned backend copy
//! (`generate_startup_object`/`_checked`/`define_cstr_data` + `exe/tests.rs`)
//! was DELETED at S113 (FIXME 0635 I3 / `audit-drain-s111.md` §1.2 disposition
//! ruling) — a superseded interim (Principle 8) that had already drifted from
//! int's live copy (Principle 7).
//!
//! What remains in this module is the [`PlatformLayoutCheck`] type: int's
//! `--link` driver consumes it (`src/exe.rs`, `src/session_v4/lifecycle.rs`)
//! to pass per-platform layout-hash checks into its own startup emission. It
//! stays in `cranelisp-backend` as the shared type on the `pub` surface.

/// A per-platform layout-hash check baked into the `--link` startup object
/// (platform-interface.md §5.5.4 `--link` gate, §7.3; BC §3 "the
/// platform-interface codegen role" point 3).
///
/// `name` is the platform name (`shapes`); `expected_hash` is the hash the
/// compiler computed from the `.cl` modules it actually compiled (via
/// `crate::schema::compute_layout_hash`). The startup stub compares
/// `expected_hash` against the statically-linked `__cranelisp_layout_hash_<name>`
/// (the DLL/rlib's embedded hash) at process start, aborting with rebuild
/// guidance on mismatch — a stale platform builds but refuses at run (the
/// accepted trade vs reading symbols out of rlib archives at build time, §1).
#[derive(Debug, Clone)]
pub struct PlatformLayoutCheck {
    /// The platform name — selects `__cranelisp_layout_hash_<name>`.
    pub name: String,
    /// The compiler-computed layout hash (from `schema::compute_layout_hash`).
    pub expected_hash: String,
}
