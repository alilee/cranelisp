//! Crate-integration compile-fixture for the `declare_platform!` macro's
//! FULL arm set — FIXME 0226 (audit C3 follow-up), filed by `/qa`.
//!
//! Role: a single `declare_platform!` invocation that exercises EVERY
//! arm of the macro in one go — `name:`, `version:`, `host:`, `schema:`,
//! `schema_types:`, and `functions:` (with all five required per-fn
//! fields: `cl_name:`, `sig:`, `doc:`, `params:`, `scheduling:`). The
//! test's job is to FAIL AT PR TIME (a compile error) if any arm is
//! silently reshaped — added, removed, renamed, or its delimiter
//! changed. It complements the `macro_expansion.rs` T17/T18 tests, which
//! assert the *behaviour* of the emitted marker types + schema static;
//! this file asserts the *compilation contract* of the macro surface
//! itself.
//!
//! The macro shape under contract is the one documented in the
//! `declare_platform!` rustdoc (`crates/cranelisp-platform/src/lib.rs`,
//! the arm table). S71 partially mitigated this gap for the NEW `schema:`
//! arm only (T17–T21); this fixture closes it for the existing arms
//! (`name:`, `version:`, `host:`, `functions:`) too, so a reshape of any
//! arm — not just the schema arm — is caught mechanically.
//!
//! spec: design/arch/facades/cranelisp-platform-audit-s69.md §4 C3
//! spec: design/arch/fixmes (FIXME 0226)

use cranelisp_platform::{HostContext, SchedulingClass};

// Static HOST required by the `host:` arm.
static FULL_ARM_HOST: HostContext = HostContext::new();

// Two extern fns referenced by the `functions:` arm. We never call them;
// they exist only so the macro has real symbols to describe.
#[allow(unsafe_op_in_unsafe_fn)]
pub extern "C" fn full_arm_noop() -> cranelisp_platform::CLIO<cranelisp_platform::CLInt> {
    cranelisp_platform::CLIO::pure(cranelisp_platform::CLInt::from(0i64))
}

#[allow(unsafe_op_in_unsafe_fn)]
pub extern "C" fn full_arm_consume(
    _x: cranelisp_platform::CLInt,
) -> cranelisp_platform::CLIO<cranelisp_platform::CLInt> {
    cranelisp_platform::CLIO::pure(cranelisp_platform::CLInt::from(0i64))
}

// The all-arms invocation. If ANY required arm is reshaped (renamed,
// removed, or its delimiter/punctuation changed), this fails to compile
// and the whole test binary fails to build — a loud PR-gate signal.
cranelisp_platform::declare_platform! {
    name: "full-arm-test",
    version: "9.9.9",
    host: FULL_ARM_HOST,
    schema: "((Rectangle ((CLInt w) (CLInt h))) (OptionInt None (Some ((CLInt val)))))",
    schema_types: [Rectangle, OptionInt],
    functions: [
        full_arm_noop {
            cl_name: "full-arm-noop",
            sig: "(Fn [] (IO Int))",
            doc: "all-arms compile witness — nullary",
            params: [],
            scheduling: SchedulingClass::Commutative,
        },
        full_arm_consume {
            cl_name: "full-arm-consume",
            sig: "(Fn [Int] (IO Int))",
            doc: "all-arms compile witness — one param",
            params: [x],
            scheduling: SchedulingClass::Sequential,
        },
    ]
}

// A trivial test body so the file is more than a compile-only fixture:
// the very existence of the emitted manifest symbol proves the macro
// expanded. (The marker-type + schema-static behaviour is asserted in
// macro_expansion.rs; here we only need the build to succeed.)
#[test]
fn full_arm_invocation_compiles_and_emits_marker_types() {
    use cranelisp_platform::CLAdtType;
    // Marker types emitted by `schema_types:` are reachable — a second,
    // cheap witness that the arm set expanded as a whole.
    assert_eq!(<Rectangle as CLAdtType>::TYPE_NAME, "Rectangle");
    assert_eq!(<OptionInt as CLAdtType>::TYPE_NAME, "OptionInt");
}
