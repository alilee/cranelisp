//! Marshal: convert between compiler Sexp and runtime Sexp ADT values.
//!
//! Used by the macro executor to pass arguments to and receive results from
//! compiled macro functions. Construction produces one owned tree. Storing a
//! child transfers its owner to the parent, and reading uses a borrow tied to
//! the live root.

use cranelisp_intrinsics::handle::{Borrowed, Owned};

use cranelisp_types::{
    NULLARY_TAG_THRESHOLD, Sexp, Span, TAG_SCONS, TAG_SEXP_ANNOTATED, TAG_SEXP_BOOL,
    TAG_SEXP_BRACKET, TAG_SEXP_FLOAT, TAG_SEXP_INT, TAG_SEXP_LIST, TAG_SEXP_STR, TAG_SEXP_SYM,
    TAG_SNIL,
};

/// NULLARY_TAG_THRESHOLD cast to i64 for comparison with runtime values.
const NULLARY_THRESHOLD: i64 = NULLARY_TAG_THRESHOLD as i64;

// Heap layout constants (from Decision 10):
// Offset 0: alloc_size (i64)
// Offset 8: rc (i64)
// Offset 16+: payload (tag at 16, fields at 24, 32, ...)
#[cfg(test)]
const RC_OFFSET: usize = 8;
const PAYLOAD_OFFSET: usize = 16;
const FIELD0_OFFSET: usize = 24;
const FIELD1_OFFSET: usize = 32;

// ---------------------------------------------------------------------------
// Sexp -> Runtime ADT (heap allocation)
// ---------------------------------------------------------------------------

/// Convert a compiler `Sexp` to a runtime Sexp ADT value (heap-allocated).
///
/// Returns the unique owner of the allocated ADT cell. Nested allocations are
/// transferred into their parent, so the returned root owns the complete tree.
pub fn sexp_to_runtime(sexp: &Sexp) -> Owned {
    match sexp {
        Sexp::Int(n, _) => alloc_sexp_cell(TAG_SEXP_INT, StoredField::Scalar(*n)),
        Sexp::Float(f, _) => {
            alloc_sexp_cell(TAG_SEXP_FLOAT, StoredField::Scalar(f.to_bits() as i64))
        }
        Sexp::Bool(b, _) => {
            alloc_sexp_cell(TAG_SEXP_BOOL, StoredField::Scalar(if *b { 1 } else { 0 }))
        }
        Sexp::Str(s, _) => {
            alloc_sexp_cell(TAG_SEXP_STR, StoredField::Owned(alloc_runtime_string(s)))
        }
        Sexp::Symbol(s, _) => {
            alloc_sexp_cell(TAG_SEXP_SYM, StoredField::Owned(alloc_runtime_string(s)))
        }
        Sexp::List(children, _) => {
            let slist = marshal_children_to_slist(children);
            alloc_sexp_cell(TAG_SEXP_LIST, StoredField::Owned(slist))
        }
        Sexp::Bracket(children, _) => {
            let slist = marshal_children_to_slist(children);
            alloc_sexp_cell(TAG_SEXP_BRACKET, StoredField::Owned(slist))
        }
        Sexp::Annotated {
            annotation,
            subject,
            ..
        } => alloc_sexp_pair(
            TAG_SEXP_ANNOTATED,
            sexp_to_runtime(annotation),
            sexp_to_runtime(subject),
        ),
        Sexp::Comment(_, _) => {
            unreachable!(
                "invariant: Comment nodes should not reach marshal (compiler pipeline uses non-preserving reader)"
            )
        }
    }
}

/// Convert a runtime Sexp ADT value back to a compiler `Sexp`.
///
/// All output spans are `Span::SYNTHETIC`; the caller rewrites them
/// to the macro call-site span.
///
/// # Preconditions
///
/// `val` must be a valid runtime Sexp ADT value: a heap pointer returned by
/// `sexp_to_runtime` or by a JIT-compiled macro function. The heap memory
/// must still be live for the duration of this borrow.
pub fn runtime_to_sexp(val: Borrowed<'_>) -> Sexp {
    let raw = val.raw_for_read();
    debug_assert!(
        raw >= NULLARY_THRESHOLD,
        "runtime_to_sexp: expected heap pointer, got bare tag {raw}"
    );

    // SAFETY: val is a heap pointer to a Sexp ADT cell allocated by
    // sexp_to_runtime or by a JIT-compiled macro function. The cell
    // has layout [header(16) | tag(8) | field0(8)].
    let tag = unsafe { read_i64(raw, PAYLOAD_OFFSET) };

    match tag {
        TAG_SEXP_INT => Sexp::Int(unsafe { read_i64(raw, FIELD0_OFFSET) }, Span::SYNTHETIC),
        TAG_SEXP_FLOAT => Sexp::Float(
            f64::from_bits(unsafe { read_i64(raw, FIELD0_OFFSET) } as u64),
            Span::SYNTHETIC,
        ),
        TAG_SEXP_BOOL => Sexp::Bool(
            unsafe { read_i64(raw, FIELD0_OFFSET) } != 0,
            Span::SYNTHETIC,
        ),
        TAG_SEXP_STR => {
            let s = read_runtime_string(unsafe { borrowed_field(val, FIELD0_OFFSET) });
            Sexp::Str(s, Span::SYNTHETIC)
        }
        TAG_SEXP_SYM => {
            let s = read_runtime_string(unsafe { borrowed_field(val, FIELD0_OFFSET) });
            Sexp::Symbol(s, Span::SYNTHETIC)
        }
        TAG_SEXP_LIST => {
            let children = read_slist_to_vec(unsafe { borrowed_field(val, FIELD0_OFFSET) });
            Sexp::List(children, Span::SYNTHETIC)
        }
        TAG_SEXP_BRACKET => {
            let children = read_slist_to_vec(unsafe { borrowed_field(val, FIELD0_OFFSET) });
            Sexp::Bracket(children, Span::SYNTHETIC)
        }
        TAG_SEXP_ANNOTATED => Sexp::Annotated {
            annotation: Box::new(runtime_to_sexp(unsafe {
                borrowed_field(val, FIELD0_OFFSET)
            })),
            subject: Box::new(runtime_to_sexp(unsafe {
                borrowed_field(val, FIELD1_OFFSET)
            })),
            span: Span::SYNTHETIC,
        },
        _ => {
            unreachable!("invariant: invalid Sexp tag {tag}")
        }
    }
}

// ---------------------------------------------------------------------------
// SList construction and reading
// ---------------------------------------------------------------------------

/// Build a runtime `(SList Sexp)` from a slice of already-marshalled i64 values.
///
/// SNil = bare tag 0 (not a heap pointer).
/// SCons = heap cell `[header(16) | tag=1(8) | head(8) | tail(8)]`.
pub fn build_runtime_slist(items: Vec<Owned>) -> Owned {
    // SAFETY: `TAG_SNIL` is the canonical produced nullary list value.
    let mut result = unsafe { Owned::from_abi(TAG_SNIL) };
    for item in items.into_iter().rev() {
        result = alloc_scons(item, result);
    }
    result
}

/// Marshal a slice of compiler Sexps into a runtime SList.
fn marshal_children_to_slist(children: &[Sexp]) -> Owned {
    let marshalled = children.iter().map(sexp_to_runtime).collect();
    build_runtime_slist(marshalled)
}

/// Read a runtime SList into a Vec of compiler Sexps.
fn read_slist_to_vec(mut slist: Borrowed<'_>) -> Vec<Sexp> {
    let mut result = Vec::new();
    loop {
        if slist.raw_for_read() < NULLARY_THRESHOLD {
            // SNil (bare tag 0) or other nullary — end of list
            debug_assert_eq!(
                slist.raw_for_read(),
                TAG_SNIL,
                "expected SNil tag, got {}",
                slist.raw_for_read()
            );
            break;
        }
        // SCons: read tag, head, tail
        // SAFETY: slist is a heap pointer to an SCons cell with layout
        // [header(16) | tag(8) | head(8) | tail(8)].
        let tag = unsafe { read_i64(slist.raw_for_read(), PAYLOAD_OFFSET) };
        debug_assert_eq!(tag, TAG_SCONS, "expected SCons tag, got {tag}");
        let head = unsafe { borrowed_field(slist, FIELD0_OFFSET) };
        let tail = unsafe { borrowed_field(slist, FIELD1_OFFSET) };
        result.push(runtime_to_sexp(head));
        slist = tail;
    }
    result
}

// ---------------------------------------------------------------------------
// Low-level allocation helpers
// ---------------------------------------------------------------------------

enum StoredField {
    Scalar(i64),
    Owned(Owned),
}

/// Allocate a Sexp cell with one field: `[header | tag | field]`.
///
/// Total payload = 8 (tag) + 8 (field) = 16 bytes.
fn alloc_sexp_cell(tag: i64, field: StoredField) -> Owned {
    let payload_size = 16; // tag(8) + field(8)
    let base = cranelisp_intrinsics::alloc::heap_alloc(payload_size);
    // SAFETY: base is a valid heap pointer with 16 bytes of payload space.
    // Tag at offset 16, field at offset 24.
    unsafe {
        write_i64(base, PAYLOAD_OFFSET, tag);
        match field {
            StoredField::Scalar(value) => write_i64(base, FIELD0_OFFSET, value),
            StoredField::Owned(owner) => write_i64(base, FIELD0_OFFSET, owner.into_raw()),
        }
    }
    // SAFETY: the fresh allocation is fully initialized at RC=1.
    unsafe { Owned::from_abi(base) }
}

/// Allocate a two-field Sexp cell: `[header | tag | field0 | field1]`.
fn alloc_sexp_pair(tag: i64, field0: Owned, field1: Owned) -> Owned {
    let payload_size = 24; // tag(8) + two fields(16)
    let base = cranelisp_intrinsics::alloc::heap_alloc(payload_size);
    // SAFETY: base is a valid heap pointer with 24 bytes of payload space.
    unsafe {
        write_i64(base, PAYLOAD_OFFSET, tag);
        write_i64(base, FIELD0_OFFSET, field0.into_raw());
        write_i64(base, FIELD1_OFFSET, field1.into_raw());
    }
    // SAFETY: the fresh allocation is fully initialized at RC=1.
    unsafe { Owned::from_abi(base) }
}

/// Allocate an SCons cell: `[header | tag=1 | head | tail]`.
///
/// Total payload = 8 (tag) + 8 (head) + 8 (tail) = 24 bytes.
fn alloc_scons(head: Owned, tail: Owned) -> Owned {
    let payload_size = 24; // tag(8) + head(8) + tail(8)
    let base = cranelisp_intrinsics::alloc::heap_alloc(payload_size);
    // SAFETY: base is a valid heap pointer with 24 bytes of payload space.
    // Tag at offset 16, head at offset 24, tail at offset 32.
    unsafe {
        write_i64(base, PAYLOAD_OFFSET, TAG_SCONS);
        write_i64(base, FIELD0_OFFSET, head.into_raw());
        write_i64(base, FIELD1_OFFSET, tail.into_raw());
    }
    // SAFETY: the fresh allocation is fully initialized at RC=1.
    unsafe { Owned::from_abi(base) }
}

// ---------------------------------------------------------------------------
// String helpers
// ---------------------------------------------------------------------------

/// Allocate a runtime string from a Rust &str. Returns the base pointer as i64.
fn alloc_runtime_string(s: &str) -> Owned {
    let bytes = s.as_bytes();
    let base =
        cranelisp_intrinsics::heap_string::heap_alloc_string(bytes.as_ptr(), bytes.len() as i64);
    // SAFETY: the intrinsic returned a fully initialized fresh RC=1 string.
    unsafe { Owned::from_abi(base) }
}

/// Read a runtime string (HeapString) back into a Rust String.
fn read_runtime_string(str_ptr: Borrowed<'_>) -> String {
    let mut out_ptr: *const u8 = std::ptr::null();
    let mut out_len: i64 = 0;
    // SAFETY: str_ptr is a valid HeapString base pointer.
    cranelisp_intrinsics::heap_string::string_read(
        str_ptr.raw_for_read(),
        &mut out_ptr,
        &mut out_len,
    );
    if out_ptr.is_null() || out_len == 0 {
        return String::new();
    }
    // SAFETY: out_ptr points to valid UTF-8 bytes of length out_len.
    let bytes = unsafe { std::slice::from_raw_parts(out_ptr, out_len as usize) };
    String::from_utf8_lossy(bytes).into_owned()
}

// ---------------------------------------------------------------------------
// Raw memory access helpers
// ---------------------------------------------------------------------------

/// Read an i64 from a base pointer at the given byte offset.
///
/// # Safety
///
/// `base` must be a valid heap pointer, and `base + offset` must be within
/// the allocation and aligned to 8 bytes.
unsafe fn read_i64(base: i64, offset: usize) -> i64 {
    unsafe { *((base as *const u8).add(offset) as *const i64) }
}

/// Write an i64 to a base pointer at the given byte offset.
///
/// # Safety
///
/// `base` must be a valid heap pointer, and `base + offset` must be within
/// the allocation and aligned to 8 bytes.
unsafe fn write_i64(base: i64, offset: usize, value: i64) {
    unsafe { *((base as *mut u8).add(offset) as *mut i64) = value }
}

/// Project a reference-bearing child through its live parent borrow.
///
/// # Safety
///
/// `offset` must identify a retained reference field in the parent's runtime
/// layout.
unsafe fn borrowed_field<'a>(parent: Borrowed<'a>, offset: usize) -> Borrowed<'a> {
    let raw = unsafe { read_i64(parent.raw_for_read(), offset) };
    // SAFETY: the caller established that the field is retained by `parent`;
    // the returned borrow is narrowed to the parent's lifetime.
    unsafe { Borrowed::from_abi(raw) }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::HeapHeader;

    // --- Byte-layout drift-guard (FIXME 0498) --------------------------------
    //
    // The offset constants in this file (`RC_OFFSET`/`PAYLOAD_OFFSET`/
    // `FIELD0_OFFSET`/`FIELD1_OFFSET`) are hardcoded literals whose rustdoc
    // *claims* they follow the `HeapHeader` base-pointer layout (Decision 10)
    // and stay byte-synced with the runtime-side marshaller
    // (`cranelisp-primitives/src/marshal.rs`, which derives the same offsets
    // from `HeapHeader::SIZE`). That was a guarding comment with no guard — the
    // "true statement that rots silently" shape the S101 `kept_jits` finding
    // flagged. These asserts turn the comment into a guard: a `HeapHeader`
    // layout change (or a careless renumber here) now trips a test instead of
    // silently corrupting the raw `read_i64`/`write_i64` accesses that read
    // these offsets.

    // spec: design/arch/fixmes/0498 — payload/tag sits immediately after the header
    #[test]
    fn payload_offset_tracks_heap_header_size() {
        assert_eq!(
            PAYLOAD_OFFSET,
            HeapHeader::SIZE,
            "ADT payload (tag) must sit at the first slot past the heap header; \
             a HeapHeader size change must be mirrored here"
        );
    }

    // spec: design/arch/fixmes/0498 — RC field offset matches the shared header layout
    #[test]
    fn rc_offset_matches_heap_header() {
        assert_eq!(
            RC_OFFSET as i32,
            HeapHeader::RC_OFFSET,
            "RC offset must match cranelisp_types::HeapHeader::RC_OFFSET (single source of truth)"
        );
    }

    // spec: design/arch/fixmes/0498 — ADT fields are i64-strided past the tag,
    // identical to the runtime-side marshaller's derived offsets.
    #[test]
    fn field_offsets_are_i64_strided_past_the_tag() {
        const STRIDE: usize = core::mem::size_of::<i64>(); // 8
        assert_eq!(
            FIELD0_OFFSET,
            PAYLOAD_OFFSET + STRIDE,
            "field 0 is one i64 past the tag"
        );
        assert_eq!(
            FIELD1_OFFSET,
            PAYLOAD_OFFSET + 2 * STRIDE,
            "field 1 is two i64s past the tag"
        );
        // Pin the concrete post-header values the raw accessors were written for
        // (mirrors the `const _` asserts on the primitives side).
        assert_eq!((PAYLOAD_OFFSET, FIELD0_OFFSET, FIELD1_OFFSET), (16, 24, 32));
    }

    // spec: design/arch/fixmes/0498 — the tag constants this file imports carry
    // the discriminant values the marshaller's match arms are written against.
    // (The canonical values also have their own guard in
    // `crates/cranelisp-types/src/marshal/tests.rs`; this is the point-of-use
    // witness on the compiler side.)
    #[test]
    fn imported_tag_constants_have_pinned_values() {
        assert_eq!((TAG_SNIL, TAG_SCONS), (0, 1));
        assert_eq!(
            (
                TAG_SEXP_INT,
                TAG_SEXP_FLOAT,
                TAG_SEXP_BOOL,
                TAG_SEXP_STR,
                TAG_SEXP_SYM,
                TAG_SEXP_LIST,
                TAG_SEXP_BRACKET,
            ),
            (0, 1, 2, 3, 4, 5, 6)
        );
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for Int
    #[test]
    fn roundtrip_int() {
        let sexp = Sexp::Int(42, Span::SYNTHETIC);
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        assert!(matches!(back, Sexp::Int(42, _)));
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for negative Int
    #[test]
    fn roundtrip_negative_int() {
        let sexp = Sexp::Int(-99, Span::SYNTHETIC);
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        assert!(matches!(back, Sexp::Int(-99, _)));
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for Float
    #[test]
    fn roundtrip_float() {
        let sexp = Sexp::Float(3.125, Span::SYNTHETIC);
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        if let Sexp::Float(f, _) = back {
            assert!((f - 3.125).abs() < f64::EPSILON);
        } else {
            panic!("expected Float");
        }
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for Bool true
    #[test]
    fn roundtrip_bool_true() {
        let sexp = Sexp::Bool(true, Span::SYNTHETIC);
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        assert!(matches!(back, Sexp::Bool(true, _)));
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for Bool false
    #[test]
    fn roundtrip_bool_false() {
        let sexp = Sexp::Bool(false, Span::SYNTHETIC);
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        assert!(matches!(back, Sexp::Bool(false, _)));
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for String
    #[test]
    fn roundtrip_str() {
        let sexp = Sexp::Str("hello".to_string(), Span::SYNTHETIC);
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        assert!(matches!(back, Sexp::Str(s, _) if s == "hello"));
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for empty String
    #[test]
    fn roundtrip_empty_str() {
        let sexp = Sexp::Str(String::new(), Span::SYNTHETIC);
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        assert!(matches!(back, Sexp::Str(s, _) if s.is_empty()));
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for Symbol
    #[test]
    fn roundtrip_sym() {
        let sexp = Sexp::Symbol("foo".to_string(), Span::SYNTHETIC);
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        assert!(matches!(back, Sexp::Symbol(s, _) if s == "foo"));
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for List
    #[test]
    fn roundtrip_list() {
        let sexp = Sexp::List(
            vec![
                Sexp::Int(1, Span::SYNTHETIC),
                Sexp::Symbol("x".to_string(), Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        if let Sexp::List(children, _) = &back {
            assert_eq!(children.len(), 2);
            assert!(matches!(&children[0], Sexp::Int(1, _)));
            assert!(matches!(&children[1], Sexp::Symbol(s, _) if s == "x"));
        } else {
            panic!("expected List, got {:?}", back);
        }
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for empty List
    #[test]
    fn roundtrip_empty_list() {
        let sexp = Sexp::List(vec![], Span::SYNTHETIC);
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        if let Sexp::List(children, _) = &back {
            assert!(children.is_empty());
        } else {
            panic!("expected empty List");
        }
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip for Bracket
    #[test]
    fn roundtrip_bracket() {
        let sexp = Sexp::Bracket(
            vec![
                Sexp::Symbol("a".to_string(), Span::SYNTHETIC),
                Sexp::Symbol("b".to_string(), Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        let rt = sexp_to_runtime(&sexp);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        if let Sexp::Bracket(children, _) = &back {
            assert_eq!(children.len(), 2);
            assert!(matches!(&children[0], Sexp::Symbol(s, _) if s == "a"));
            assert!(matches!(&children[1], Sexp::Symbol(s, _) if s == "b"));
        } else {
            panic!("expected Bracket");
        }
    }

    // spec: 09-macros.md section 9.7 — SList round-trip
    #[test]
    fn roundtrip_slist() {
        let items = vec![
            sexp_to_runtime(&Sexp::Int(10, Span::SYNTHETIC)),
            sexp_to_runtime(&Sexp::Int(20, Span::SYNTHETIC)),
            sexp_to_runtime(&Sexp::Int(30, Span::SYNTHETIC)),
        ];
        let slist = build_runtime_slist(items);
        let back = read_slist_to_vec(slist.as_borrowed());
        cranelisp_intrinsics::drop::consume_slist(slist);
        assert_eq!(back.len(), 3);
        assert!(matches!(&back[0], Sexp::Int(10, _)));
        assert!(matches!(&back[1], Sexp::Int(20, _)));
        assert!(matches!(&back[2], Sexp::Int(30, _)));
    }

    // spec: 09-macros.md section 9.7 — empty SList round-trip
    #[test]
    fn roundtrip_empty_slist() {
        let slist = build_runtime_slist(Vec::new());
        assert_eq!(slist.raw_for_read(), TAG_SNIL);
        let back = read_slist_to_vec(slist.as_borrowed());
        cranelisp_intrinsics::drop::consume_slist(slist);
        assert!(back.is_empty());
    }

    // -----------------------------------------------------------------------
    // S122 — single-owner macro marshalling.
    //
    // The seam is unit-testable with no JIT session: marshal an arg, then read
    // the RC of EVERY cell the marshaller allocated. Each is born at RC=1:
    // an interior cell is owned by its unique parent and the returned handle
    // owns the root.
    // -----------------------------------------------------------------------

    fn cell_rc(base: i64) -> i64 {
        // SAFETY: `base` is a live heap cell allocated by the marshaller.
        unsafe { read_i64(base, RC_OFFSET) }
    }

    /// Collect the RC of every heap cell reachable in a marshalled runtime Sexp
    /// tree: the Sexp cell, both children of Annotated, its `HeapString`
    /// (Str/Sym), and every SList spine SCons cell + its element cells
    /// (recursively).
    fn collect_cell_rcs(base: i64, out: &mut Vec<(&'static str, i64)>) {
        if base < NULLARY_THRESHOLD {
            return; // bare nullary tag (SNil) — not a heap cell
        }
        out.push(("cell", cell_rc(base)));
        // SAFETY: `base` is a live Sexp cell: tag@16, field0@24.
        let tag = unsafe { read_i64(base, PAYLOAD_OFFSET) };
        let field0 = unsafe { read_i64(base, FIELD0_OFFSET) };
        match tag {
            TAG_SEXP_STR | TAG_SEXP_SYM => {
                if field0 >= NULLARY_THRESHOLD {
                    out.push(("string", cell_rc(field0)));
                }
            }
            TAG_SEXP_LIST | TAG_SEXP_BRACKET => collect_slist_rcs(field0, out),
            TAG_SEXP_ANNOTATED => {
                let field1 = unsafe { read_i64(base, FIELD1_OFFSET) };
                collect_cell_rcs(field0, out);
                collect_cell_rcs(field1, out);
            }
            _ => {}
        }
    }

    fn collect_slist_rcs(mut slist: i64, out: &mut Vec<(&'static str, i64)>) {
        while slist >= NULLARY_THRESHOLD {
            out.push(("scons", cell_rc(slist)));
            // SAFETY: SCons cell: head@24, tail@32.
            let head = unsafe { read_i64(slist, FIELD0_OFFSET) };
            let tail = unsafe { read_i64(slist, FIELD1_OFFSET) };
            collect_cell_rcs(head, out);
            slist = tail;
        }
    }

    // spec: design/int/macro-turn-ownership.md Rule 1 — one structural owner
    // exists for every cell before the argument root crosses the ABI.
    #[test]
    fn marshalled_tree_is_single_owner_at_every_depth() {
        // A nested arg exercising interior cells + spine + HeapStrings:
        // (SexpList [a (SexpList [b 1]) "d"]).
        let arg = Sexp::List(
            vec![
                Sexp::Symbol("a".to_string(), Span::SYNTHETIC),
                Sexp::List(
                    vec![
                        Sexp::Symbol("b".to_string(), Span::SYNTHETIC),
                        Sexp::Int(1, Span::SYNTHETIC),
                    ],
                    Span::SYNTHETIC,
                ),
                Sexp::Str("d".to_string(), Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        let rt = sexp_to_runtime(&arg);
        let mut rcs = Vec::new();
        collect_cell_rcs(rt.raw_for_read(), &mut rcs);
        // The tree has interior structure (root cell, spine, element cells,
        // nested list, HeapStrings) — many cells, not just the top.
        assert!(rcs.len() >= 6, "expected a deep single-owner tree: {rcs:?}");
        for (kind, rc) in &rcs {
            assert_eq!(
                *rc, 1,
                "every marshalled {kind} cell must have exactly one owner: {rcs:?}"
            );
        }
        cranelisp_intrinsics::drop::consume_sexp(rt);
    }

    // spec: design/int/macro-turn-ownership.md Rule 1 — every runtime cell kind
    // emitted by the marshaller follows the same single-owner rule.
    #[test]
    fn single_owner_completeness_over_cell_kinds() {
        // One arg of each cell kind the marshaller can allocate.
        let args = vec![
            Sexp::Int(7, Span::SYNTHETIC),
            Sexp::Float(1.5, Span::SYNTHETIC),
            Sexp::Bool(true, Span::SYNTHETIC),
            Sexp::Str("s".to_string(), Span::SYNTHETIC),
            Sexp::Symbol("y".to_string(), Span::SYNTHETIC),
            Sexp::List(vec![Sexp::Int(2, Span::SYNTHETIC)], Span::SYNTHETIC),
            Sexp::Bracket(
                vec![Sexp::Symbol("z".to_string(), Span::SYNTHETIC)],
                Span::SYNTHETIC,
            ),
            Sexp::Annotated {
                annotation: Box::new(Sexp::Symbol("tag".to_string(), Span::SYNTHETIC)),
                subject: Box::new(Sexp::Str("value".to_string(), Span::SYNTHETIC)),
                span: Span::SYNTHETIC,
            },
        ];
        for arg in &args {
            let rt = sexp_to_runtime(arg);
            let mut rcs = Vec::new();
            collect_cell_rcs(rt.raw_for_read(), &mut rcs);
            assert!(!rcs.is_empty());
            if matches!(arg, Sexp::Annotated { .. }) {
                assert_eq!(
                    rcs.len(),
                    5,
                    "Annotated completeness must visit its root, both child cells and both child strings: {rcs:?}"
                );
            }
            for (kind, rc) in &rcs {
                assert_eq!(
                    *rc, 1,
                    "cell kind {kind} of {arg:?} must have exactly one owner: {rcs:?}"
                );
            }
            cranelisp_intrinsics::drop::consume_sexp(rt);
        }
    }

    // spec: design/int/macro-turn-ownership.md Rule 1 — the argument SList spine
    // follows the same single-owner construction rule.
    #[test]
    fn args_slist_spine_is_single_owner() {
        let items = vec![
            sexp_to_runtime(&Sexp::Int(1, Span::SYNTHETIC)),
            sexp_to_runtime(&Sexp::Int(2, Span::SYNTHETIC)),
        ];
        let slist = build_runtime_slist(items);
        let mut rcs = Vec::new();
        collect_slist_rcs(slist.raw_for_read(), &mut rcs);
        assert!(
            rcs.iter().any(|(k, _)| *k == "scons"),
            "expected spine cells: {rcs:?}"
        );
        for (kind, rc) in &rcs {
            assert_eq!(
                *rc, 1,
                "args-SList {kind} cell must have exactly one owner: {rcs:?}"
            );
        }
        cranelisp_intrinsics::drop::consume_slist(slist);
    }

    // spec: 09-macros.md section 9.7 — nested List round-trip
    #[test]
    fn roundtrip_nested_list() {
        let inner = Sexp::List(
            vec![Sexp::Int(1, Span::SYNTHETIC), Sexp::Int(2, Span::SYNTHETIC)],
            Span::SYNTHETIC,
        );
        let outer = Sexp::List(vec![inner, Sexp::Int(3, Span::SYNTHETIC)], Span::SYNTHETIC);
        let rt = sexp_to_runtime(&outer);
        let back = runtime_to_sexp(rt.as_borrowed());
        cranelisp_intrinsics::drop::consume_sexp(rt);
        if let Sexp::List(children, _) = &back {
            assert_eq!(children.len(), 2);
            if let Sexp::List(inner_children, _) = &children[0] {
                assert_eq!(inner_children.len(), 2);
                assert!(matches!(&inner_children[0], Sexp::Int(1, _)));
                assert!(matches!(&inner_children[1], Sexp::Int(2, _)));
            } else {
                panic!("expected nested List");
            }
            assert!(matches!(&children[1], Sexp::Int(3, _)));
        } else {
            panic!("expected outer List");
        }
    }

    // spec: design/int/macro-turn-ownership.md D3 — an undisposed marshal
    // root is caught at the frame by the typed handle's debug drop bomb.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "LEAKED Owned heap handle")]
    fn undisposed_marshaled_root_triggers_the_drop_bomb() {
        let _owner = sexp_to_runtime(&Sexp::Int(1, Span::SYNTHETIC));
    }
}
