//! Scheduling class for platform functions.
//!
//! `SchedulingClass` is plain manifest data attached to platform DLL
//! functions. It governs two things:
//!
//! 1. How `bind!` chains are compiled — sequential-chain vs. parallel-safe.
//! 2. How the IO trampoline schedules nodes during IO forcing.
//!
//! The type lives at the bottom of the dependency DAG (`cranelisp-types`)
//! so that it can appear both on `PrimitiveKind::PlatformEffect` (a variant
//! field on `ModuleEntry::Def.kind`) and in the platform-ABI surface
//! (`cranelisp-platform::PlatformFn::scheduling_class`) without forcing a
//! `cranelisp-types -> cranelisp-platform` dependency edge (which would
//! violate Principle 3 — `cranelisp-types` depends on nothing).
//!
//! `cranelisp-platform` re-exports this type as `cranelisp_platform::SchedulingClass`
//! so every existing consumer (platform DLLs, `declare_platform!` macro
//! users) continues to compile unchanged.

use serde::{Deserialize, Serialize};

/// Scheduling class for a platform function, declared in the platform manifest.
///
/// Controls how `bind!` chains are compiled and how the IO trampoline
/// schedules parallel execution.
#[repr(u32)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum SchedulingClass {
    /// Always execute in order relative to other effects -- global shared resource
    /// (e.g. stdin, stdout, a global log). Never placed in a Par node.
    #[default]
    Sequential = 0,
    /// Fully independent -- no shared state between calls. Always safe to parallelize
    /// with other Commutative effects (e.g. HTTP requests, time queries, `open`).
    Commutative = 1,
    /// Parallel across different resource tokens; sequential within the same token.
    /// The platform function sets the token via `CLIO::effect_on_resource(token, ...)`.
    ResourceSerial = 2,
}

impl SchedulingClass {
    /// Convert a u32 discriminant to SchedulingClass, defaulting to Sequential on unknown values.
    pub fn from_u32(v: u32) -> Self {
        match v {
            1 => Self::Commutative,
            2 => Self::ResourceSerial,
            _ => Self::Sequential,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_is_sequential() {
        assert_eq!(SchedulingClass::default(), SchedulingClass::Sequential);
    }

    #[test]
    fn from_u32_maps_known_discriminants() {
        assert_eq!(SchedulingClass::from_u32(0), SchedulingClass::Sequential);
        assert_eq!(SchedulingClass::from_u32(1), SchedulingClass::Commutative);
        assert_eq!(SchedulingClass::from_u32(2), SchedulingClass::ResourceSerial);
        assert_eq!(SchedulingClass::from_u32(99), SchedulingClass::Sequential);
    }

    #[test]
    fn serde_roundtrip_preserves_variant() {
        for cls in [
            SchedulingClass::Sequential,
            SchedulingClass::Commutative,
            SchedulingClass::ResourceSerial,
        ] {
            let json = serde_json::to_string(&cls).expect("serialize");
            let rt: SchedulingClass = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(cls, rt);
        }
    }
}
