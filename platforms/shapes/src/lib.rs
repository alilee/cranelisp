//! `shapes` platform for cranelisp -- the ADT-typed test-DLL fixture.
//!
//! Sprint 79 Wave 0. The first platform DLL whose function signatures
//! reference a user-defined ADT (`shapes/Rectangle`), so the backend emits a
//! NON-EMPTY schema + `__cranelisp_layout_hash_shapes`, and the host's
//! GOT-indirect dispatch arm (apply.rs) + host-side ADT marshaling
//! (`alloc_with_tag`) are exercised end-to-end for the first time.
//!
//! Unlike `stdio`/`test-capture` (scalar-only platforms), `shapes` marshals an
//! ADT across the FFI boundary. Platforms do NOT declare ADTs -- `Rectangle`
//! is an ordinary `.cl` type (see `shapes.cl`). The DLL only embeds the
//! compiler-generated *schema artifact* (`shapes.platform-schema`), which maps
//! field NAMES (`w`/`h`) to byte offsets so `read_field("w")` resolves.
//!
//! ## The fixture contract (agreed S79 Phase 3; /qa drives this exact interface)
//! - Platform name: `shapes`. ABI v3.
//! - ADT: `Rectangle` = `(deftype Rectangle [:Int w :Int h])`, FQ identity
//!   `shapes/Rectangle` (defined in `shapes.cl`, not here).
//! - Platform fn: `rectangle_area(r: CLAdt<Rectangle>) -> CLIO<CLInt>`, reading
//!   `w`/`h` BY NAME inside a deferred IO Effect, returning `w*h`.
//!   `cl_name: "area"`,
//!   `sig: "(Fn [shapes/Rectangle] (primitives/IO primitives/Int))"`,
//!   `scheduling: SchedulingClass::Commutative`. All platform fns MUST return
//!   `IO _` (FIXME 0318 — foreign purity is unverifiable).
//! - Contract: `(area (Rectangle 3 4))` ⇒ 12.
//!
//! Uses the `cranelisp-platform` shared crate for ABI types, the `CLAdt<T>`
//! ADT-marshaling wrapper, and the `declare_platform!` macro's `schema:` embed
//! arm.

use cranelisp_platform::*;

static HOST: HostContext = HostContext::new();

/// Marker type for the `shapes/Rectangle` ADT parameter.
///
/// Carries the fully-qualified cranelisp type identity that
/// [`CLAdt::read_field`] uses to look the layout up in the embedded schema. No
/// fields -- `CLAdt<Rectangle>` is `#[repr(transparent)]` over the heap
/// pointer; field access is schema-driven, not via Rust struct layout.
pub struct Rectangle;

impl CLAdtType for Rectangle {
    const TYPE_NAME: &'static str = "shapes/Rectangle";
}

/// Compute the area of a `Rectangle` by reading its two `Int` fields by NAME
/// from the embedded schema and multiplying them. Returns a deferred IO Effect
/// (all platform fns MUST return `IO _` — FIXME 0318: foreign purity is
/// unverifiable, so the only sound treatment of foreign code is to sequence its
/// effects through the trampoline).
///
/// `read_field::<CLInt>("w")` / `("h")` resolve the byte offset from the
/// process-global schema installed at DLL load (the embedded
/// `shapes.platform-schema` artifact); the layout-hash gate (host-side) refuses
/// a schema that does not match the host's live-tables regeneration before this
/// ever runs.
///
/// ## IO-returning pattern (mirrors `stdio::print_string`)
/// Like `print`/`read-line`, this extern returns its value through the
/// trampoline as a `CLIO::effect(move || ...)` thunk rather than computing
/// eagerly. The work (`w*h` → 12) runs when the Effect is forced.
///
/// ## RC note (Discovery R4)
/// `Rectangle` is a heap ADT, so under the consuming calling convention
/// (Decision 24) the caller transfers its reference to us. Following the
/// `stdio` capture-RC protocol, `into_owned_consuming` adopts the transferred
/// reference (no inc on wrap) and the resulting `CLOwned` is captured by-move
/// into the Effect closure; it releases the reference on drop when the thunk
/// runs. The field reads happen inside the thunk against the still-live
/// allocation (`CLOwned` derefs to `CLAdt<Rectangle>`). `CLAdt<T>` is `Copy`
/// and `'static` (a transparent pointer wrapper over a marker type), so the
/// owned handle is `'static`-capturable. Net RC: caller +1 (transfer) →
/// `CLOwned` drop −1 = balanced.
pub extern "C" fn rectangle_area(r: CLAdt<Rectangle>) -> CLIO<CLInt> {
    // Adopt the caller-transferred reference; released on drop when the Effect
    // thunk runs (consuming capture-RC protocol, Decision 24).
    let owned = <CLAdt<Rectangle> as CLHeap>::into_owned_consuming(r);
    CLIO::effect(move || {
        let w: CLInt = owned.read_field("w");
        let h: CLInt = owned.read_field("h");
        CLInt::from(i64::from(w) * i64::from(h))
    })
}

declare_platform! {
    name: "shapes",
    version: "0.1.0",
    host: HOST,
    schema: include_str!("shapes.platform-schema"), // GENERATED -- regenerated via /platform-schema after R2 lands
    functions: [
        rectangle_area {
            cl_name: "area",
            sig: "(Fn [shapes/Rectangle] (primitives/IO primitives/Int))",
            doc: "Compute the area of a rectangle (w * h), reading fields by name across the FFI boundary",
            params: [r],
            scheduling: SchedulingClass::Commutative,
        },
    ]
}
