//! S68 — backend dep-ban: `cranelisp-backend` MUST NOT depend on
//! `cranelisp-primitives`.
//!
//! Per Decision 0048 §"Structural invariant — backend dep-ban" and
//! Principle 18 (enforce architectural invariants structurally where
//! possible). The architectural invariant "primitives dispatch reaches
//! code via GOT, never via direct extern" is enforced structurally by
//! the workspace DAG — backend has no Rust-path visibility into
//! primitives' fns, so the only available dispatch is the type-erased
//! `SymbolTable` + `GotTable` mechanism in `cranelisp-types`.
//!
//! This test lives next to the crate it polices (rather than under
//! `tests/facade_compliance.rs`) so the assertion runs whenever the
//! backend crate is tested, including in isolation, and so the test
//! reads the backend's *own* Cargo.toml via `CARGO_MANIFEST_DIR`
//! without needing a workspace-root walk.
//!
//! **Failing-now-fail-until-impl-lands.** At authoring time (S68 Phase 5
//! Stage 1) `crates/cranelisp-backend/Cargo.toml` still lists
//! `cranelisp-primitives` under `[dependencies]` (the pre-S68 state).
//! The test is expected to FAIL until Wave 4 lands the atomic edit pair
//! (delete backend's dep; add primitives' dep on backend for the
//! `Code::Primitive` variant). Per
//! `memory/feedback_failing_not_ignored.md` it is NOT `#[ignore]`'d.

use std::fs;
use std::path::PathBuf;

// spec: design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md
//       §"Structural invariant — backend dep-ban";
//       design/arch/principles/18-enforce-invariants-structurally.md
//
// Architectural invariant: cranelisp-backend MUST NOT depend on cranelisp-primitives.
// The dispatch invariant ("primitives reach code via GOT, never via direct extern")
// is enforced structurally by the workspace DAG — backend has no Rust-path
// visibility into primitives' fns. This test reads backend's Cargo.toml and
// asserts the structural property. Supersedes earlier CLIF-shape-inspection
// proposal.
#[test]
fn s68_backend_does_not_depend_on_primitives() {
    let manifest_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let cargo_toml = fs::read_to_string(&manifest_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", manifest_path.display()));

    // Strict-but-simple scan: the dep line is `cranelisp-primitives = { path = "..." }`
    // (table form) or `cranelisp-primitives = "..."` (version form). A bare substring
    // check on `"cranelisp-primitives"` covers both. The Cargo.toml is small and
    // structured; the only mentions would be a dep line or a comment naming the
    // crate. A comment mention would also be a contract violation (the dep was
    // there or is being added).
    //
    // Failing-now (pre-Wave-4): `cranelisp-primitives` is listed under [dependencies].
    // Will pass after Wave 4 dep removal lands.
    assert!(
        !cargo_toml.contains("cranelisp-primitives"),
        "cranelisp-backend MUST NOT depend on cranelisp-primitives per \
         Decision 0048 §\"Structural invariant — backend dep-ban\". \
         Workspace DAG enforces the GOT-dispatch invariant structurally. \
         Wave 4 of S68 deletes the dep line as part of the atomic edit pair \
         (backend dep removed; primitives dep on backend added for Code::Primitive). \
         Cargo.toml at {}:\n{}",
        manifest_path.display(),
        cargo_toml,
    );
}
