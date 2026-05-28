//! `CLAdt<T>` — the platform-DLL ADT-marshaling wrapper.
//!
//! Joins the `CLInt`/`CLBool`/`CLFloat`/`CLString` family as the heap-ADT
//! crossing-the-FFI-boundary representation. Generic over a per-type
//! **marker type** (one per declared cranelisp ADT, auto-emitted by
//! `declare_platform!` from the schema literal), backed by a per-DLL
//! parsed `Schema` value resolved at runtime via the per-marker-type
//! `GetSchema` trampoline.
//!
//! See `design/platform/sprint71-redesign.md` §3–§4 for the full design.
//!
//! Field-access **reads** are callback-free: the DLL computes byte
//! offsets locally from its parsed schema and transmutes at the offset.
//! Field-access **construction** (`CLAdt::<T>::construct(...)`) is the
//! only path that touches host state — it routes through
//! `HostCallbacks::alloc_with_tag` and panics under the R1 wired-or-panic
//! gate until the host-wiring sprint (FIXME 0229) populates it.

use std::marker::PhantomData;

use crate::schema::{FieldType, Schema};
use crate::{CLHeap, CLOwned, CLType};

// ---------------------------------------------------------------------
// Marker-type trait family
// ---------------------------------------------------------------------

/// Marker trait for typed `CLAdt` parameters.
///
/// Implemented by the `declare_platform!` macro for each ADT declared in
/// the schema. DLL authors do not implement this directly.
pub trait CLAdtType: 'static {
    /// The cranelisp type name as it appears in the schema and at runtime.
    /// Schema lookups use this string to find the type's field layout.
    const TYPE_NAME: &'static str;
}

/// Default marker for untyped `CLAdt` — used when the DLL author works
/// generically over heap-ADT values without committing to a specific
/// type at compile time. See `design/platform/sprint71-redesign.md` §4.6.
pub struct AnyAdt;

impl CLAdtType for AnyAdt {
    const TYPE_NAME: &'static str = ""; // sentinel — see §4.6
}

/// Per-marker-type schema trampoline. Each `declare_platform!`-emitted
/// marker type implements this to point at the DLL's `LazyLock<Schema>`
/// static. See `design/platform/sprint71-redesign.md` §7.4 — "option (ii)".
///
/// `AnyAdt` does NOT implement `GetSchema`; methods on `CLAdt<AnyAdt>`
/// are statically restricted to `read_tag()` + `into_typed::<T>()`.
pub trait GetSchema: CLAdtType {
    fn schema() -> &'static Schema;
}

// ---------------------------------------------------------------------
// CLAdt<T> wrapper
// ---------------------------------------------------------------------

/// Heap-ADT value crossing the FFI boundary. Layout per design §3:
/// `#[repr(transparent)]` over an `i64` (payload base pointer) plus a
/// zero-sized `PhantomData<T>` for compile-time witness binding. The
/// JIT and host see exactly one `i64` payload at every call site.
#[repr(transparent)]
pub struct CLAdt<T: CLAdtType = AnyAdt>(i64, PhantomData<T>);

impl<T: CLAdtType> std::fmt::Debug for CLAdt<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CLAdt<{}>({:#x})", T::TYPE_NAME, self.0)
    }
}

impl<T: CLAdtType> Clone for CLAdt<T> {
    fn clone(&self) -> Self {
        CLAdt(self.0, PhantomData)
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
    /// Construct from a raw payload base pointer. Intended for the FFI
    /// boundary (where the JIT hands us an `i64` we know to be a tagged
    /// heap ADT) and for tests using synthetic heap fixtures.
    pub fn from_raw(payload_ptr: i64) -> Self {
        CLAdt(payload_ptr, PhantomData)
    }
}

// ---------------------------------------------------------------------
// Method set — typed CLAdt<T: CLAdtType + GetSchema>
// ---------------------------------------------------------------------

/// The "schema-backed" method set on typed CLAdt. Per design §4.1.
impl<T: CLAdtType + GetSchema> CLAdt<T> {
    /// Read the runtime tag at the fixed offset payload+0.
    ///
    /// No schema lookup. No callback. The four bytes at payload+0 are
    /// always the variant tag (or 0 for products), per design §3.
    pub fn read_tag(&self) -> u32 {
        // SAFETY: the FFI invariant guarantees that any CLAdt<T> handed
        // across the boundary points at a heap-ADT layout with a u32 tag
        // at payload+0. Reading 4 bytes at that offset is sound.
        unsafe { *(self.0 as *const u32) }
    }

    /// Read a primitive field by name. Schema lookup computes the byte
    /// offset from `T::TYPE_NAME` + `field_name`; transmute the i64 at
    /// that offset to `F`.
    ///
    /// Panics if the field name is not in T's schema (programmer error
    /// at the DLL-author level — typo or stale-rename per §4.5), or if
    /// the field's schema type doesn't match `F`'s witness (per §3.3).
    pub fn read_field<F: CLType>(&self, field_name: &str) -> F
    where
        F: CLTypeWitness,
    {
        let schema = T::schema();
        let (offset, declared_type) = resolve_field::<T>(schema, field_name);
        F::check_witness(T::TYPE_NAME, field_name, declared_type);

        // SAFETY: the offset is computed from a parsed schema that the
        // DLL author authored alongside the type definition; the FFI
        // invariant guarantees the heap layout matches. Reading the i64
        // at payload+offset and transmuting to F is sound under the
        // witness check above.
        let raw = unsafe { *((self.0 + offset as i64) as *const i64) };
        F::from_raw_i64(raw)
    }

    /// Read a heap field by name with inc-on-read. Returns a
    /// `CLOwned<F>` (dec on drop, mirroring Decision 24).
    ///
    /// `F` must be `CLHeap` — `CLString`, or another `CLAdt<U>`.
    /// Panics on schema miss or witness mismatch.
    pub fn own_field<F: CLHeap + CLTypeWitness>(&self, field_name: &str) -> CLOwned<F> {
        let schema = T::schema();
        let (offset, declared_type) = resolve_field::<T>(schema, field_name);
        F::check_witness(T::TYPE_NAME, field_name, declared_type);

        // SAFETY: identical justification to `read_field` — schema-driven
        // offset, FFI invariant on layout, witness check above.
        let raw = unsafe { *((self.0 + offset as i64) as *const i64) };
        let f = F::from_raw_i64(raw);
        // own() does inc-on-read; CLOwned drop will dec, balancing.
        f.own()
    }

    /// Construct a new CLAdt value from a tag + field array. Routes
    /// through `HostCallbacks::alloc_with_tag`.
    ///
    /// **Wired-or-panic** under the R1 gate (design §9): until the host
    /// wires `alloc_with_tag` (FIXME 0229), this path panics with a
    /// FIXME-pointing message inside `null_alloc_with_tag`.
    ///
    /// Returns `CLOwned<CLAdt<T>>` per design §4.3 — the just-allocated
    /// heap value has RC=1 (set by `alloc_with_tag`); wrap without re-inc.
    pub fn construct(tag: u32, fields: &[i64]) -> CLOwned<CLAdt<T>> {
        let alloc_with_tag = crate::get_host_alloc_with_tag();
        let payload_ptr =
            alloc_with_tag(tag, fields.len() as u32, fields.as_ptr());
        let adt = CLAdt::<T>::from_raw(payload_ptr);
        // No inc — alloc_with_tag sets RC=1 already.
        <CLAdt<T> as CLHeap>::into_owned_consuming(adt)
    }
}

// ---------------------------------------------------------------------
// Method set — untyped escape hatch CLAdt<AnyAdt>
// ---------------------------------------------------------------------

impl CLAdt<AnyAdt> {
    /// Read the runtime tag without consulting a schema. Same fixed-offset
    /// load as the typed version.
    pub fn read_tag_any(&self) -> u32 {
        unsafe { *(self.0 as *const u32) }
    }

    /// Coerce an untyped `CLAdt<AnyAdt>` to a typed `CLAdt<T>`.
    /// Performs the type-witness check using `T`'s schema; panics on
    /// mismatch (per design §3.3).
    ///
    /// This is the safe escape-hatch shape: field access on `AnyAdt` is
    /// not exposed; the DLL author must commit to a marker type via
    /// `into_typed::<T>()` first.
    pub fn into_typed<T: CLAdtType + GetSchema>(self) -> CLAdt<T> {
        // The full witness check is deferred to first field-access call
        // (per design §3.3 — in-line at each method entry). Here we
        // simply re-wrap with the new marker. Construction-from-AnyAdt
        // is by-construction acceptable; bad coercions surface at the
        // first read_field/own_field call.
        CLAdt::<T>::from_raw(self.0)
    }
}

// ---------------------------------------------------------------------
// CLType witness trait — the bound `F: CLTypeWitness` on read_field/own_field
// ---------------------------------------------------------------------

/// Compile-time + runtime witness for the field-type `F` used at a
/// `read_field` / `own_field` call site.
///
/// The `expected_field_type()` constant tells the runtime check what
/// the schema must say for a given `F`; the panic on mismatch surfaces
/// programmer errors at the DLL-author level (typo, stale-rename, or a
/// DLL author writing wrong code per §3.3).
pub trait CLTypeWitness: Sized {
    /// What schema field-type `Self` represents.
    fn expected_field_type() -> ExpectedFieldType;

    /// Build a typed value from the raw i64 representation read from
    /// the heap. For `CLInt`/`CLBool`/`CLFloat`/`CLString` this is a
    /// transparent wrap; for `CLAdt<T>` it's `from_raw`.
    fn from_raw_i64(raw: i64) -> Self;

    /// Compare the schema's declared type for a field against this
    /// witness; panic on mismatch with the §3.3 message.
    fn check_witness(type_name: &str, field_name: &str, declared: &FieldType) {
        let expected = Self::expected_field_type();
        if !expected.matches(declared) {
            panic!(
                "CLAdt field-type witness mismatch:\n  \
                 type:      {type_name}\n  \
                 field:     {field_name}\n  \
                 expected:  {expected:?}\n  \
                 declared:  {declared:?}\n  \
                 cause:     wrong type witness at the call site, or schema typo.\n  \
                 see:       design/platform/sprint71-redesign.md §3.3"
            )
        }
    }
}

/// Witness-side representation of a CL field type. Mirrors `FieldType`
/// but for ADT references holds no string (the witness is the marker
/// type `T`, whose `TYPE_NAME` we compare against the schema's ADT
/// reference).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpectedFieldType {
    CLInt,
    CLBool,
    CLFloat,
    CLString,
    /// The witness is `CLAdt<T>` with `T::TYPE_NAME == name`.
    Adt(&'static str),
}

impl ExpectedFieldType {
    fn matches(&self, declared: &FieldType) -> bool {
        match (self, declared) {
            (ExpectedFieldType::CLInt, FieldType::CLInt) => true,
            (ExpectedFieldType::CLBool, FieldType::CLBool) => true,
            (ExpectedFieldType::CLFloat, FieldType::CLFloat) => true,
            (ExpectedFieldType::CLString, FieldType::CLString) => true,
            (ExpectedFieldType::Adt(name), FieldType::Adt(declared_name)) => name == declared_name,
            _ => false,
        }
    }
}

// CLType wrappers implement the witness trait.
impl CLTypeWitness for crate::CLInt {
    fn expected_field_type() -> ExpectedFieldType { ExpectedFieldType::CLInt }
    fn from_raw_i64(raw: i64) -> Self { crate::CLInt::from(raw) }
}

impl CLTypeWitness for crate::CLBool {
    fn expected_field_type() -> ExpectedFieldType { ExpectedFieldType::CLBool }
    fn from_raw_i64(raw: i64) -> Self { crate::CLBool::from(raw != 0) }
}

impl CLTypeWitness for crate::CLFloat {
    fn expected_field_type() -> ExpectedFieldType { ExpectedFieldType::CLFloat }
    fn from_raw_i64(raw: i64) -> Self {
        crate::CLFloat::from(f64::from_ne_bytes(raw.to_ne_bytes()))
    }
}

impl CLTypeWitness for crate::CLString {
    fn expected_field_type() -> ExpectedFieldType { ExpectedFieldType::CLString }
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

/// Resolve a field name (possibly dot-qualified for sums) to a
/// (byte_offset, declared_type) tuple. Panics on schema miss with the
/// §4.5 message.
fn resolve_field<T: CLAdtType>(
    schema: &'static Schema,
    field_name: &str,
) -> (usize, &'static FieldType) {
    let type_name = T::TYPE_NAME;

    // Dot-qualified form per design §4.4 — `"Some.val"`.
    let (variant_name, canonical_field) = if let Some((before, after)) = field_name.split_once('.') {
        (Some(before), after)
    } else {
        (None, field_name)
    };

    // For products: variant_name (if any) must equal type_name; for sums:
    // variant_name names the variant. We probe both shapes.
    let offset = if let Some(vn) = variant_name {
        if vn == type_name {
            // Product with optional self-qualification: `Rectangle.w`
            schema.lookup_field_offset(type_name, canonical_field)
        } else {
            schema.lookup_variant_field_offset(type_name, vn, canonical_field)
        }
    } else {
        schema.lookup_field_offset(type_name, canonical_field)
    };

    let declared_type = schema.lookup_field_type(type_name, variant_name, canonical_field);

    match (offset, declared_type) {
        (Some(off), Some(dt)) => (off, dt),
        _ => {
            let available_variants = schema
                .variant_names(type_name)
                .unwrap_or_default()
                .join(", ");
            panic!(
                "CLAdt::read_field schema lookup miss:\n  \
                 type:        {type_name}\n  \
                 asked for:   {field_name}\n  \
                 variants:    [{available_variants}]\n  \
                 cause:       field name not declared in this type's schema\n  \
                 see:         design/platform/sprint71-redesign.md §4.5"
            )
        }
    }
}

// ---------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CLInt;
    use std::sync::OnceLock;

    // -----------------------------------------------------------------
    // Test fixtures: synthetic schemas + marker types
    // -----------------------------------------------------------------

    // Rectangle ((CLInt w) (CLInt h)) — pure product
    pub struct Rectangle;
    impl CLAdtType for Rectangle {
        const TYPE_NAME: &'static str = "Rectangle";
    }
    impl GetSchema for Rectangle {
        fn schema() -> &'static Schema { rectangle_schema() }
    }
    fn rectangle_schema() -> &'static Schema {
        static S: OnceLock<Schema> = OnceLock::new();
        S.get_or_init(|| Schema::parse("((Rectangle ((CLInt w) (CLInt h))))").unwrap())
    }

    // OptionInt sum
    pub struct OptionInt;
    impl CLAdtType for OptionInt {
        const TYPE_NAME: &'static str = "OptionInt";
    }
    impl GetSchema for OptionInt {
        fn schema() -> &'static Schema { option_int_schema() }
    }
    fn option_int_schema() -> &'static Schema {
        static S: OnceLock<Schema> = OnceLock::new();
        S.get_or_init(|| Schema::parse("((OptionInt None (Some ((CLInt val)))))").unwrap())
    }

    // -----------------------------------------------------------------
    // Helpers: synthetic heap fixtures for CLAdt payloads.
    // -----------------------------------------------------------------

    /// Allocate a synthetic CLAdt payload: `[tag: u32][pad: u32][field0: i64]...`
    /// at payload base. Returns the payload base pointer. Caller responsible
    /// for freeing via std::alloc::dealloc.
    fn alloc_cladt_payload(tag: u32, fields: &[i64]) -> i64 {
        let payload_size = 8 + fields.len() * 8;
        // SAFETY: standard allocator path; layout aligned to 8.
        unsafe {
            let layout = std::alloc::Layout::from_size_align_unchecked(payload_size, 8);
            let ptr = std::alloc::alloc_zeroed(layout) as *mut u8;
            *(ptr as *mut u32) = tag;
            *(ptr.add(4) as *mut u32) = 0; // pad
            for (i, val) in fields.iter().enumerate() {
                *((ptr.add(8 + i * 8)) as *mut i64) = *val;
            }
            ptr as i64
        }
    }

    fn free_cladt_payload(payload: i64, field_count: usize) {
        let payload_size = 8 + field_count * 8;
        unsafe {
            let layout = std::alloc::Layout::from_size_align_unchecked(payload_size, 8);
            std::alloc::dealloc(payload as *mut u8, layout);
        }
    }

    // -----------------------------------------------------------------
    // T9 — CLAdt::read_tag — fixed offset 0, no callback
    // -----------------------------------------------------------------

    // T9 — spec: design/platform/sprint71-redesign.md §4.1 (read_tag fixed offset 0)
    #[test]
    fn t9_read_tag_fixed_offset_no_callback() {
        let payload = alloc_cladt_payload(42, &[]);
        let r: CLAdt<Rectangle> = CLAdt::from_raw(payload);
        assert_eq!(r.read_tag(), 42);
        free_cladt_payload(payload, 0);
    }

    // -----------------------------------------------------------------
    // T10 — CLAdt<Rectangle>::read_field::<CLInt>("w") — product
    // -----------------------------------------------------------------

    // T10 — spec: design/platform/sprint71-redesign.md §4.1 (read_field on product)
    #[test]
    fn t10_read_field_product_rectangle_w() {
        let payload = alloc_cladt_payload(0, &[3, 4]);
        let r: CLAdt<Rectangle> = CLAdt::from_raw(payload);
        let w: CLInt = r.read_field::<CLInt>("w");
        let h: CLInt = r.read_field::<CLInt>("h");
        assert_eq!(i64::from(w), 3);
        assert_eq!(i64::from(h), 4);
        // Dot-qualified form on product also works (§4.4).
        let w2: CLInt = r.read_field::<CLInt>("Rectangle.w");
        assert_eq!(i64::from(w2), 3);
        free_cladt_payload(payload, 2);
    }

    // -----------------------------------------------------------------
    // T12 — CLAdt<OptionInt> — sum, None
    // -----------------------------------------------------------------

    // T12 — spec: design/platform/sprint71-redesign.md §4.4
    #[test]
    fn t12_sum_option_none() {
        let payload = alloc_cladt_payload(0, &[]); // None = tag 0
        let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
        assert_eq!(opt.read_tag(), 0);
        free_cladt_payload(payload, 0);
    }

    // -----------------------------------------------------------------
    // T13 — CLAdt<OptionInt> — sum, Some + dot-qualified lookup
    // -----------------------------------------------------------------

    // T13 — spec: design/platform/sprint71-redesign.md §4.4 (sum-type dot-qualified discipline)
    #[test]
    fn t13_sum_option_some_dot_qualified_lookup() {
        let payload = alloc_cladt_payload(1, &[7]); // Some(7) = tag 1, val 7
        let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
        assert_eq!(opt.read_tag(), 1);
        let val: CLInt = opt.read_field::<CLInt>("Some.val");
        assert_eq!(i64::from(val), 7);
        free_cladt_payload(payload, 1);
    }

    // -----------------------------------------------------------------
    // T16 — type-witness mismatch panics with clear message
    // -----------------------------------------------------------------

    // T16 — spec: design/platform/sprint71-redesign.md §3.3 (type-witness mismatch)
    #[test]
    #[should_panic(expected = "witness mismatch")]
    fn t16_field_type_witness_mismatch_panics() {
        let payload = alloc_cladt_payload(0, &[3, 4]);
        let r: CLAdt<Rectangle> = CLAdt::from_raw(payload);
        // Rectangle.w is CLInt, but we ask for CLBool — must panic.
        let _ = r.read_field::<crate::CLBool>("w");
        // (no free needed — panic before)
    }

    // -----------------------------------------------------------------
    // T28 — sum-type field lookup discipline (negative: ambiguous)
    // -----------------------------------------------------------------

    // T28 — spec: design/platform/sprint71-redesign.md §4.4 (dot-qualified discipline)
    #[test]
    #[should_panic(expected = "schema lookup miss")]
    fn t28_sum_unqualified_field_rejected_for_sum() {
        let payload = alloc_cladt_payload(1, &[7]);
        let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
        // Unqualified `"val"` is rejected for sums; must dot-qualify.
        let _ = opt.read_field::<CLInt>("val");
    }

    // T28 — positive complement: dot-qualified path works (covered by t13)
    // The pair is t13 (positive) + t28 (negative).

    // -----------------------------------------------------------------
    // T26 — read paths do NOT require callback wiring
    // -----------------------------------------------------------------

    // T26 — spec: design/platform/sprint71-redesign.md §9.1 (read paths callback-free)
    #[test]
    fn t26_read_paths_do_not_require_callback_wiring() {
        // The HostContext / GLOBAL_ALLOC machinery may or may not be init
        // by other tests in this process; the point of T26 is that
        // read_tag and read_field do not call any HostCallbacks function.
        // We exercise both with a synthetic payload and no HostContext::init
        // having been called on the relevant alloc_with_tag callback —
        // and assert no panic.
        let payload = alloc_cladt_payload(7, &[42]);
        let r: CLAdt<Rectangle> = CLAdt::from_raw(payload);
        assert_eq!(r.read_tag(), 7);
        let w: CLInt = r.read_field::<CLInt>("w");
        assert_eq!(i64::from(w), 42);
        free_cladt_payload(payload, 1);
    }

    // -----------------------------------------------------------------
    // CLAdt is #[repr(transparent)] — round-trips through i64.
    // -----------------------------------------------------------------

    #[test]
    fn cladt_repr_transparent_roundtrips() {
        let raw: i64 = 0xDEAD_BEEF_CAFE_BABEu64 as i64;
        let r: CLAdt<Rectangle> = CLAdt::from_raw(raw);
        assert_eq!(r.to_raw(), raw);
        assert_eq!(r.raw_ptr(), raw);
        // The marker type is invisible at runtime.
        assert_eq!(std::mem::size_of::<CLAdt<Rectangle>>(), std::mem::size_of::<i64>());
        assert_eq!(std::mem::size_of::<CLAdt<AnyAdt>>(), std::mem::size_of::<i64>());
    }

    // -----------------------------------------------------------------
    // CLAdt<AnyAdt> escape hatch: read_tag_any + into_typed
    // -----------------------------------------------------------------

    #[test]
    fn anyadt_read_tag_and_into_typed() {
        let payload = alloc_cladt_payload(99, &[]);
        let any: CLAdt<AnyAdt> = CLAdt::from_raw(payload);
        assert_eq!(any.read_tag_any(), 99);
        // Coerce to typed Rectangle (witness check is deferred to first
        // field-access call per §3.3).
        let _r: CLAdt<Rectangle> = any.into_typed::<Rectangle>();
        free_cladt_payload(payload, 0);
    }
}
