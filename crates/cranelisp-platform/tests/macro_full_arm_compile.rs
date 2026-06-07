//! Crate-integration compile-fixture for the `declare_platform!` macro's
//! FULL arm set — the all-arms compile contract (originally FIXME 0226,
//! reworked for the three-exports model under FIXME 0286).
//!
//! Role: a single `declare_platform!` invocation that exercises EVERY arm of
//! the (reworked) macro in one go — `name:`, `version:`, `host:`, the `schema:`
//! EMBED arm (the generated artifact text), and `functions:` (with all five
//! required per-fn fields: `cl_name:`, `sig:`, `doc:`, `params:`,
//! `scheduling:`). The test's job is to FAIL AT PR TIME (a compile error) if
//! any arm is silently reshaped — added, removed, renamed, or its delimiter
//! changed.
//!
//! The macro shape under contract is the one documented in the
//! `declare_platform!` rustdoc (`crates/cranelisp-platform/src/lib.rs`, the arm
//! table). Per FIXME 0286 / platform-interface.md §6.1–§6.6 the macro now emits
//! the exported GOT (`__cranelisp_got_platform_<name>`) + manifest + (for the
//! `schema:` arm) the embedded generated schema and the layout-hash export
//! (`__cranelisp_layout_hash_<name>`). The schema *declaration* dialect +
//! `schema_types:` + marker-type auto-emission are retired; this fixture uses
//! the embed arm with an author-defined marker type, the target shape.
//!
//! spec: design/arch/platform-interface.md §6.1 (macro arms) / §6.6 (retirement)

use cranelisp_platform::{CLAdtType, HostContext, SchedulingClass};

// Static HOST required by the `host:` arm.
static FULL_ARM_HOST: HostContext = HostContext::new();

// An author-defined marker type keyed by FQ name — the post-S71 shape (the
// macro no longer auto-emits these from a declaration DSL).
struct Rectangle;
impl CLAdtType for Rectangle {
    const TYPE_NAME: &'static str = "shapes/Rectangle";
}

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

// The all-arms invocation, WITH the `schema:` embed arm. The schema text is the
// generated-artifact grammar (not the retired declaration dialect). If ANY
// required arm is reshaped (renamed, removed, or its delimiter/punctuation
// changed), this fails to compile — a loud PR-gate signal.
cranelisp_platform::declare_platform! {
    name: "full-arm-test",
    version: "9.9.9",
    host: FULL_ARM_HOST,
    schema: "\
;; layout-hash: fullarmtest
(schema
  (shapes/Rectangle
    (Rectangle 0 ((w primitives/Int) (h primitives/Int)))))",
    functions: [
        full_arm_noop {
            cl_name: "full-arm-noop",
            sig: "(Fn [] (IO primitives/Int))",
            doc: "all-arms compile witness — nullary",
            params: [],
            scheduling: SchedulingClass::Commutative,
        },
        full_arm_consume {
            cl_name: "full-arm-consume",
            sig: "(Fn [shapes/Rectangle] (IO primitives/Int))",
            doc: "all-arms compile witness — one param",
            params: [x],
            scheduling: SchedulingClass::Sequential,
        },
    ]
}

// A trivial test body so the file is more than a compile-only fixture. The
// marker type is reachable (a second, cheap witness that the arm set expanded
// as a whole). The macro-emitted GOT/manifest/layout-hash exports are exercised
// by `macro_expansion.rs`.
#[test]
fn full_arm_invocation_compiles() {
    assert_eq!(<Rectangle as CLAdtType>::TYPE_NAME, "shapes/Rectangle");
}
