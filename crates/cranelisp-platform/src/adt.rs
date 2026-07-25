//! `CLAdt<T>` — the platform-DLL ADT-marshaling wrapper.
//!
//! Joins the `CLInt`/`CLBool`/`CLFloat`/`CLString` family as the heap-ADT
//! crossing-the-FFI-boundary representation. `CLAdt<T>` is `#[repr(transparent)]`
//! over the alloc-base `i64`; the marker type `T` carries the cranelisp
//! **fully-qualified** type name ([`CLAdtType::TYPE_NAME`], e.g.
//! `"shapes/Rectangle"`) that keys into the DLL's embedded schema.
//!
//! # Field access is by NAME, against the embedded generated schema
//!
//! Per the platform-interface rework (`design/arch/platform-interface.md`
//! §5.5, user-ratified 2026-06-07; FIXME 0286): a platform no longer *declares*
//! its ADTs. Its data types are ordinary `.cl` modules; the DLL embeds a
//! **compiler-generated schema artifact** (`declare_platform! { schema:
//! include_str!("<name>.platform-schema"), … }`) that records the transitive
//! closure of every ADT the platform's signatures reach. The macro parses that
//! artifact once into a per-DLL [`crate::Schema`] and installs it as the
//! process-global schema ([`set_global_schema`]); [`CLAdt::read_field`] reads
//! a field **by name**, resolving its byte offset + declared [`FieldType`]
//! from that schema (the typed fields drive nested-ADT navigation — a field
//! whose type is `geometry/Point` is looked up *by its key* in the same map).
//!
//! This **retires the Sprint 71 marker-type DSL**: the hand-authored schema
//! *declaration* arm, the `LazyLock<Schema>`-as-DSL static, the
//! `GetSchema`-per-type trampoline, and the `AnyAdt` escape hatch are gone. The
//! schema is one machine-written artifact per DLL, not a per-type declaration.
//!
//! # Read vs construction paths
//!
//! Field-access **reads** ([`CLAdt::read_field`] / [`CLAdt::own_field`] /
//! [`CLAdt::read_tag`]) are **callback-free**: the DLL computes the byte offset
//! locally from the embedded schema and transmutes at the offset. No host
//! round-trip per read.
//!
//! Field-access **construction** ([`CLAdt::construct`]) is the only path that
//! touches host state — it routes through [`crate::HostCallbacks::alloc_with_tag`]
//! (wired by the host since S76; `alloc_with_tag` is KEPT — ADT construction
//! across the FFI still needs the host allocator, orthogonal to the schema
//! retirement, `platform-interface.md` §6.6).
//!
//! See `design/arch/platform-interface.md` §4–§5.5 (the platform-author
//! experience + the field-by-name design) and `design/arch/bounded-contexts.md`
//! §5 for the cross-surface story.

use std::marker::PhantomData;
use std::sync::OnceLock;

use crate::schema::{FieldType, Schema};
use crate::{CLHeap, CLOwned, CLType, HEAP_HEADER_SIZE};

// ---------------------------------------------------------------------
// Marker-type trait
// ---------------------------------------------------------------------

/// Marker trait for typed `CLAdt` parameters — carries the cranelisp
/// **fully-qualified** type name used to key the embedded schema.
///
/// A DLL author declares one zero-sized marker per ADT they marshal, e.g.
///
/// ```ignore
/// pub struct Rectangle;
/// impl cranelisp_platform::CLAdtType for Rectangle {
///     const TYPE_NAME: &'static str = "shapes/Rectangle";
/// }
/// ```
///
/// (The Sprint 71 `declare_platform!` schema arm auto-emitted these from the
/// declaration DSL; with the DSL retired the author writes the marker directly
/// — a few lines, no generated declaration — or a future ergonomic layer
/// generates them. The marker carries only the FQ key string; the layout comes
/// from the embedded schema, not the marker.)
pub trait CLAdtType: 'static {
    /// The cranelisp FQ type-key as it appears in the embedded schema and in
    /// the function signatures (`"shapes/Rectangle"`). Schema lookups use this
    /// string to find the type's field layout.
    const TYPE_NAME: &'static str;
}

// ---------------------------------------------------------------------
// Process-global embedded schema
// ---------------------------------------------------------------------

/// The DLL's embedded, parsed schema. Installed once by the `declare_platform!`
/// `schema:` embed arm (which parses `include_str!("<name>.platform-schema")`);
/// read by `CLAdt`'s field-access methods.
///
/// Each DLL is its own compilation unit, so this static is per-DLL. The schema
/// is a single artifact per platform (the transitive closure of every ADT the
/// platform's sigs reach), so one global is the right cardinality.
static GLOBAL_SCHEMA: OnceLock<Schema> = OnceLock::new();

/// Install the DLL's parsed schema. Called by the `declare_platform!` macro's
/// `schema:` embed arm. Idempotent — a second install is ignored (the embed
/// arm runs once).
pub fn set_global_schema(schema: Schema) {
    let _ = GLOBAL_SCHEMA.set(schema);
}

/// The DLL's embedded schema. Panics if the DLL did not embed one (a
/// programmer error: `read_field` was called on a platform that declared no
/// `schema:` arm). Construction-only / scalar-only DLLs never reach this.
fn global_schema() -> &'static Schema {
    GLOBAL_SCHEMA.get().unwrap_or_else(|| {
        panic!(
            "CLAdt field access requires an embedded schema, but this platform \
             DLL did not embed one. Add `schema: include_str!(\"<name>.platform-schema\")` \
             to declare_platform! and regenerate the artifact with /platform-schema. \
             See design/arch/platform-interface.md §5.5."
        )
    })
}

// ---------------------------------------------------------------------
// CLAdt<T> wrapper
// ---------------------------------------------------------------------

/// Heap-ADT value crossing the FFI boundary. The stored `i64` is the **alloc
/// base pointer** (the `[total_size: i64][rc: i64][tag: u32][pad: u32][fields…]`
/// allocation's address). `read_tag` / `read_field` add [`HEAP_HEADER_SIZE`]
/// (16) to reach the payload; `inc_rc` / `dec_rc` from [`CLHeap`] use `base + 8`
/// to find the RC field. Mirrors `CLString`'s base-pointer convention.
///
/// `#[repr(transparent)]` over `i64` plus a zero-sized `PhantomData<T>` for the
/// compile-time type-key witness; the JIT and host see exactly one `i64`.
#[repr(transparent)]
pub struct CLAdt<T: CLAdtType>(i64, PhantomData<T>);

impl<T: CLAdtType> std::fmt::Debug for CLAdt<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CLAdt<{}>({:#x})", T::TYPE_NAME, self.0)
    }
}

impl<T: CLAdtType> Clone for CLAdt<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: CLAdtType> Copy for CLAdt<T> {}

impl<T: CLAdtType> CLType for CLAdt<T> {
    fn to_raw(self) -> i64 {
        self.0
    }
}

impl<T: CLAdtType> CLHeap for CLAdt<T> {
    fn raw_ptr(&self) -> i64 {
        self.0
    }
}

impl<T: CLAdtType> CLAdt<T> {
    /// Construct from a raw **alloc base** pointer (the address of the
    /// `[total_size][rc][tag][pad][fields…]` heap allocation). Intended for the
    /// FFI boundary (where the JIT hands us an `i64` known to be a tagged heap
    /// ADT) and for tests using synthetic heap fixtures.
    pub fn from_raw(base_ptr: i64) -> Self {
        CLAdt(base_ptr, PhantomData)
    }

    /// Compute the payload pointer (base + [`HEAP_HEADER_SIZE`]).
    fn payload_ptr(&self) -> i64 {
        self.0 + HEAP_HEADER_SIZE
    }

    /// Read the runtime tag at the fixed offset payload+0.
    ///
    /// No schema lookup. The four bytes at payload+0 are always the variant tag
    /// (or 0 for products).
    pub fn read_tag(&self) -> u32 {
        // SAFETY: the FFI invariant guarantees any CLAdt<T> handed across the
        // boundary points at a heap-ADT layout with a u32 tag at payload+0.
        unsafe { *(self.payload_ptr() as *const u32) }
    }

    /// Read a primitive field **by name**, resolving the byte offset from the
    /// embedded schema for `T::TYPE_NAME`. Sum-type fields are named
    /// dot-qualified (`"Some.val"`); product fields plain (`"w"`) or
    /// self-qualified (`"Rectangle.w"`).
    ///
    /// Panics if the field is not in the schema, or if the schema's declared
    /// field type does not match `F`'s witness.
    pub fn read_field<F>(&self, field_name: &str) -> F
    where
        F: CLType + CLTypeWitness,
    {
        let (offset, declared) = resolve_field::<T>(field_name);
        F::check_witness(T::TYPE_NAME, field_name, declared);
        // SAFETY: the offset is computed from the embedded schema, which the
        // compiler generated from the same resolved module graph the host
        // compiles; the layout-hash gate refuses a stale schema. Reading the
        // i64 at payload+offset and transmuting to F is sound under the witness
        // check above.
        let raw = unsafe { *((self.payload_ptr() + offset as i64) as *const i64) };
        F::from_raw_i64(raw)
    }

    /// Read a heap field by name with inc-on-read. Returns a [`CLOwned<F>`]
    /// (dec on drop, mirroring Decision 24). `F` must be [`CLHeap`].
    pub fn own_field<F: CLHeap + CLTypeWitness>(&self, field_name: &str) -> CLOwned<F> {
        let (offset, declared) = resolve_field::<T>(field_name);
        F::check_witness(T::TYPE_NAME, field_name, declared);
        // SAFETY: identical to `read_field` — schema-driven offset, FFI layout
        // invariant, witness check above.
        let raw = unsafe { *((self.payload_ptr() + offset as i64) as *const i64) };
        let f = F::from_raw_i64(raw);
        f.own()
    }

    /// Construct a new `CLAdt` value from a tag + field array, via the host's
    /// [`crate::HostCallbacks::alloc_with_tag`]. Returns `CLOwned<CLAdt<T>>` —
    /// the just-allocated value has RC=1 (set by `alloc_with_tag`); wrap
    /// without re-inc.
    pub fn construct(tag: u32, fields: &[i64]) -> CLOwned<CLAdt<T>> {
        let alloc_with_tag = crate::get_host_alloc_with_tag();
        let payload_ptr = alloc_with_tag(tag, fields.len() as u32, fields.as_ptr());
        let adt = CLAdt::<T>::from_raw(payload_ptr);
        <CLAdt<T> as CLHeap>::into_owned_consuming(adt)
    }
}

// ---------------------------------------------------------------------
// CLType witness trait — the bound `F: CLTypeWitness` on read_field/own_field
// ---------------------------------------------------------------------

/// Compile-time + runtime witness for the field-type `F` at a `read_field` /
/// `own_field` call site, checked against the embedded schema's declared
/// [`FieldType`].
pub trait CLTypeWitness: Sized {
    /// What schema field-type `Self` represents.
    fn expected_field_type() -> ExpectedFieldType;

    /// Build a typed value from the raw i64 read from the heap.
    fn from_raw_i64(raw: i64) -> Self;

    /// Compare the schema's declared type for a field against this witness;
    /// panic on mismatch.
    fn check_witness(type_name: &str, field_name: &str, declared: &FieldType) {
        let expected = Self::expected_field_type();
        if !expected.matches(declared) {
            panic!(
                "CLAdt field-type witness mismatch:\n  \
                 type:      {type_name}\n  \
                 field:     {field_name}\n  \
                 expected:  {expected:?}\n  \
                 declared:  {declared:?}\n  \
                 cause:     wrong type witness at the call site, or a stale schema.\n  \
                 see:       design/arch/platform-interface.md §5.5"
            )
        }
    }
}

/// Witness-side representation of a CL field type. Compared against the
/// embedded schema's [`FieldType`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpectedFieldType {
    Int,
    Bool,
    Float,
    String,
    /// The witness is `CLAdt<T>` with `T::TYPE_NAME == key`.
    Adt(&'static str),
}

impl ExpectedFieldType {
    fn matches(&self, declared: &FieldType) -> bool {
        match (self, declared) {
            (ExpectedFieldType::Int, FieldType::Scalar(n)) => n == "primitives/Int",
            (ExpectedFieldType::Bool, FieldType::Scalar(n)) => n == "primitives/Bool",
            (ExpectedFieldType::Float, FieldType::Scalar(n)) => n == "primitives/Float",
            (ExpectedFieldType::String, FieldType::Scalar(n)) => n == "primitives/String",
            // An ADT-typed field: the witness marker's key must match the
            // declared ADT's name (args ignored — the marker pins the head).
            (ExpectedFieldType::Adt(key), FieldType::Adt(name, _)) => key == name,
            _ => false,
        }
    }
}

impl CLTypeWitness for crate::CLInt {
    fn expected_field_type() -> ExpectedFieldType {
        ExpectedFieldType::Int
    }
    fn from_raw_i64(raw: i64) -> Self {
        crate::CLInt::from(raw)
    }
}

impl CLTypeWitness for crate::CLBool {
    fn expected_field_type() -> ExpectedFieldType {
        ExpectedFieldType::Bool
    }
    fn from_raw_i64(raw: i64) -> Self {
        crate::CLBool::from(raw != 0)
    }
}

impl CLTypeWitness for crate::CLFloat {
    fn expected_field_type() -> ExpectedFieldType {
        ExpectedFieldType::Float
    }
    fn from_raw_i64(raw: i64) -> Self {
        crate::CLFloat::from(f64::from_ne_bytes(raw.to_ne_bytes()))
    }
}

impl CLTypeWitness for crate::CLString {
    fn expected_field_type() -> ExpectedFieldType {
        ExpectedFieldType::String
    }
    fn from_raw_i64(raw: i64) -> Self {
        // SAFETY: CLString is #[repr(transparent)] over i64; this is the
        // standard wrap used at FFI boundaries.
        unsafe { std::mem::transmute::<i64, crate::CLString>(raw) }
    }
}

impl<T: CLAdtType> CLTypeWitness for CLAdt<T> {
    fn expected_field_type() -> ExpectedFieldType {
        ExpectedFieldType::Adt(T::TYPE_NAME)
    }
    fn from_raw_i64(raw: i64) -> Self {
        CLAdt::<T>::from_raw(raw)
    }
}

// ---------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------

/// Resolve a field name (possibly dot-qualified for sums) against the embedded
/// schema to a `(byte_offset, declared_type)` tuple. Panics on schema miss.
fn resolve_field<T: CLAdtType>(field_name: &str) -> (usize, &'static FieldType) {
    let schema = global_schema();
    let type_key = T::TYPE_NAME;

    // Dot-qualified form — `"Some.val"` names a sum-type constructor; a
    // self-qualified `"Rectangle.w"` on a product strips to the bare field.
    let (ctor_name, canonical_field): (Option<&str>, &str) = match field_name.split_once('.') {
        Some((before, after)) => (Some(before), after),
        None => (None, field_name),
    };

    // For a product, a self-qualifier (`Rectangle.w`) names the type, not a
    // distinct constructor — treat it as unqualified.
    let ctor_for_lookup = match ctor_name {
        Some(cn) if cn == type_key_tail(type_key) => None,
        other => other,
    };

    let offset = schema.field_offset(type_key, ctor_for_lookup, canonical_field);
    let declared = schema.field_type(type_key, ctor_for_lookup, canonical_field);

    match (offset, declared) {
        (Some(off), Some(dt)) => (off, dt),
        _ => {
            let ctors = schema.ctor_names(type_key).unwrap_or_default().join(", ");
            panic!(
                "CLAdt::read_field schema lookup miss:\n  \
                 type:        {type_key}\n  \
                 asked for:   {field_name}\n  \
                 constructors:[{ctors}]\n  \
                 cause:       field name not in this type's embedded schema (or a \
                              sum-type field was not dot-qualified)\n  \
                 see:         design/arch/platform-interface.md §5.5"
            )
        }
    }
}

/// The unqualified type name of an FQ key (`"shapes/Rectangle"` → `"Rectangle"`)
/// — used to recognise a self-qualifying field prefix on a product.
fn type_key_tail(key: &str) -> &str {
    key.rsplit('/').next().unwrap_or(key)
}

// ---------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests;
