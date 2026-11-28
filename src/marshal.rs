//! Marshal: convert between compiler Sexp and runtime Sexp ADT values.
//!
//! Used by the macro executor to pass arguments to and receive results from
//! compiled macro functions. Construction produces one owned tree. Storing a
//! child transfers its owner to the parent, and reading uses a borrow tied to
//! the live root.

use std::collections::HashSet;

use cranelisp_intrinsics::alloc::HeapAdt;
use cranelisp_intrinsics::handle::{Borrowed, Owned};

use cranelisp_types::{
    NULLARY_TAG_THRESHOLD, Sexp, Span, TAG_SCONS, TAG_SEXP_ANNOTATED, TAG_SEXP_BOOL,
    TAG_SEXP_BRACKET, TAG_SEXP_FLOAT, TAG_SEXP_INT, TAG_SEXP_LIST, TAG_SEXP_STR, TAG_SEXP_SYM,
    TAG_SNIL,
};

/// NULLARY_TAG_THRESHOLD cast to i64 for comparison with runtime values.
const NULLARY_THRESHOLD: i64 = NULLARY_TAG_THRESHOLD as i64;

// Sexp and SList cells are data-constructor values; their layout is
// `HeapAdt`'s (BC §4b invariant 2).
const TAG_OFFSET: usize = HeapAdt::TAG_OFFSET as usize;
const FIELD0_OFFSET: usize = HeapAdt::field_offset(0) as usize;
const FIELD1_OFFSET: usize = HeapAdt::field_offset(1) as usize;

// ---------------------------------------------------------------------------
// Sexp -> Runtime ADT (heap allocation)
// ---------------------------------------------------------------------------

/// Convert a compiler `Sexp` to a runtime Sexp ADT value (heap-allocated).
///
/// Returns the unique owner of the allocated ADT cell. Nested allocations are
/// transferred into their parent, so the returned root owns the complete tree.
#[cfg(test)]
pub fn sexp_to_runtime(sexp: &Sexp) -> Owned {
    marshal(sexp, &mut |_| {})
}

/// One macro call's marshalled argument list, and a held reference on the
/// name string of every argument symbol
/// (`design/int/expansion-qualification-scope.md` §2.7).
pub(crate) struct ClauseCall {
    pub(crate) args: Owned,
    pub(crate) held: HeldSymbolNames,
}

/// References the host holds on argument symbol names for one clause call. A
/// held string's count is never one, so it is neither freed nor rewritten in
/// place, and its address names it alone while the call lasts. It is released
/// only by [`take_clause_result`].
pub(crate) struct HeldSymbolNames(Vec<Owned>);

impl HeldSymbolNames {
    fn identities(&self) -> HashSet<i64> {
        self.0.iter().map(Owned::raw_for_read).collect()
    }

    fn release(self) {
        for name in self.0 {
            cranelisp_intrinsics::rc::consume_shallow(name);
        }
    }
}

/// Marshal a macro call's arguments into one owned runtime list, holding a
/// reference on each argument symbol's name.
pub(crate) fn marshal_clause_call(args: &[Sexp]) -> ClauseCall {
    let mut held = Vec::new();
    let mut hold = |name: Borrowed<'_>| held.push(name.to_owned());
    let marshalled = args.iter().map(|arg| marshal(arg, &mut hold)).collect();
    ClauseCall {
        args: build_runtime_slist(marshalled),
        held: HeldSymbolNames(held),
    }
}

/// A clause's result copied to a compiler `Sexp`, with fresh synthetic spans.
/// `caller_text` holds the span of every symbol whose name is one of the call's
/// held argument strings.
pub(crate) struct Expansion {
    pub(crate) sexp: Sexp,
    pub(crate) caller_text: HashSet<Span>,
}

/// A clause returned a bare tag where a `Sexp` heap value is required.
#[derive(Debug)]
pub(crate) struct InvalidClauseResult(pub(crate) i64);

/// Adopt a clause's result word, copy it, and release the result and the held
/// argument names exactly once, on both outcomes.
pub(crate) fn take_clause_result(
    result_word: i64,
    held: HeldSymbolNames,
) -> Result<Expansion, InvalidClauseResult> {
    // SAFETY: the macro-clause ABI transfers one owned Sexp result word to the
    // host. Bare nullary tags are valid `Owned` values and consume as a no-op.
    let result = unsafe { Owned::from_abi(result_word) };
    let outcome = if result.is_nullary_tag() {
        Err(InvalidClauseResult(result_word))
    } else {
        let mut reader = Unmarshal {
            caller_names: held.identities(),
            caller_text: HashSet::new(),
            span: cranelisp_frontend::next_synthetic_span,
        };
        let sexp = reader.read(result.as_borrowed());
        Ok(Expansion {
            sexp,
            caller_text: reader.caller_text,
        })
    };
    cranelisp_intrinsics::drop::consume_sexp(result);
    held.release();
    outcome
}

/// Marshal `sexp`, offering each symbol's name string to `hold` before the
/// string is stored in its cell.
fn marshal(sexp: &Sexp, hold: &mut dyn FnMut(Borrowed<'_>)) -> Owned {
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
            let name = alloc_runtime_string(s);
            hold(name.as_borrowed());
            alloc_sexp_cell(TAG_SEXP_SYM, StoredField::Owned(name))
        }
        Sexp::List(children, _) => {
            let slist = marshal_children_to_slist(children, hold);
            alloc_sexp_cell(TAG_SEXP_LIST, StoredField::Owned(slist))
        }
        Sexp::Bracket(children, _) => {
            let slist = marshal_children_to_slist(children, hold);
            alloc_sexp_cell(TAG_SEXP_BRACKET, StoredField::Owned(slist))
        }
        Sexp::Annotated {
            annotation,
            subject,
            ..
        } => alloc_sexp_pair(
            TAG_SEXP_ANNOTATED,
            marshal(annotation, hold),
            marshal(subject, hold),
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
/// All output spans are `Span::SYNTHETIC`.
///
/// # Preconditions
///
/// `val` must be a valid runtime Sexp ADT value: a heap pointer returned by
/// `sexp_to_runtime` or by a JIT-compiled macro function. The heap memory
/// must still be live for the duration of this borrow.
#[cfg(test)]
pub fn runtime_to_sexp(val: Borrowed<'_>) -> Sexp {
    Unmarshal {
        caller_names: HashSet::new(),
        caller_text: HashSet::new(),
        span: || Span::SYNTHETIC,
    }
    .read(val)
}

/// One copy of a runtime Sexp tree. Each node takes a span from `span`; a
/// symbol whose name string is one of `caller_names` records its span in
/// `caller_text`.
struct Unmarshal {
    caller_names: HashSet<i64>,
    caller_text: HashSet<Span>,
    span: fn() -> Span,
}

impl Unmarshal {
    /// Copy the live runtime Sexp `val`, which must be a heap value allocated
    /// by the marshaller or by compiled macro code.
    fn read(&mut self, val: Borrowed<'_>) -> Sexp {
        let raw = val.raw_for_read();
        debug_assert!(
            raw >= NULLARY_THRESHOLD,
            "runtime_to_sexp: expected heap pointer, got bare tag {raw}"
        );

        // SAFETY: val is a heap pointer to a Sexp ADT cell allocated by
        // sexp_to_runtime or by a JIT-compiled macro function. The cell
        // has the `HeapAdt` layout [header | tag | field0 | ...].
        let tag = unsafe { read_i64(raw, TAG_OFFSET) };

        match tag {
            TAG_SEXP_INT => Sexp::Int(unsafe { read_i64(raw, FIELD0_OFFSET) }, (self.span)()),
            TAG_SEXP_FLOAT => Sexp::Float(
                f64::from_bits(unsafe { read_i64(raw, FIELD0_OFFSET) } as u64),
                (self.span)(),
            ),
            TAG_SEXP_BOOL => {
                Sexp::Bool(unsafe { read_i64(raw, FIELD0_OFFSET) } != 0, (self.span)())
            }
            TAG_SEXP_STR => {
                let s = read_runtime_string(unsafe { borrowed_field(val, FIELD0_OFFSET) });
                Sexp::Str(s, (self.span)())
            }
            TAG_SEXP_SYM => {
                let name = unsafe { borrowed_field(val, FIELD0_OFFSET) };
                let span = (self.span)();
                if self.caller_names.contains(&name.raw_for_read()) {
                    self.caller_text.insert(span);
                }
                Sexp::Symbol(read_runtime_string(name), span)
            }
            TAG_SEXP_LIST => {
                let children = self.read_slist(unsafe { borrowed_field(val, FIELD0_OFFSET) });
                Sexp::List(children, (self.span)())
            }
            TAG_SEXP_BRACKET => {
                let children = self.read_slist(unsafe { borrowed_field(val, FIELD0_OFFSET) });
                Sexp::Bracket(children, (self.span)())
            }
            TAG_SEXP_ANNOTATED => Sexp::Annotated {
                annotation: Box::new(self.read(unsafe { borrowed_field(val, FIELD0_OFFSET) })),
                subject: Box::new(self.read(unsafe { borrowed_field(val, FIELD1_OFFSET) })),
                span: (self.span)(),
            },
            _ => {
                unreachable!("invariant: invalid Sexp tag {tag}")
            }
        }
    }

    /// Copy a runtime SList into a Vec of compiler Sexps.
    fn read_slist(&mut self, mut slist: Borrowed<'_>) -> Vec<Sexp> {
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
            // [header | tag | head | tail].
            let tag = unsafe { read_i64(slist.raw_for_read(), TAG_OFFSET) };
            debug_assert_eq!(tag, TAG_SCONS, "expected SCons tag, got {tag}");
            let head = unsafe { borrowed_field(slist, FIELD0_OFFSET) };
            let tail = unsafe { borrowed_field(slist, FIELD1_OFFSET) };
            result.push(self.read(head));
            slist = tail;
        }
        result
    }
}

// ---------------------------------------------------------------------------
// SList construction and reading
// ---------------------------------------------------------------------------

/// Build a runtime `(SList Sexp)` from a slice of already-marshalled i64 values.
///
/// SNil = bare tag 0 (not a heap pointer).
/// SCons = heap cell `[header | tag=1 | head | tail]`.
pub fn build_runtime_slist(items: Vec<Owned>) -> Owned {
    // SAFETY: `TAG_SNIL` is the canonical produced nullary list value.
    let mut result = unsafe { Owned::from_abi(TAG_SNIL) };
    for item in items.into_iter().rev() {
        result = alloc_scons(item, result);
    }
    result
}

/// Marshal a slice of compiler Sexps into a runtime SList.
fn marshal_children_to_slist(children: &[Sexp], hold: &mut dyn FnMut(Borrowed<'_>)) -> Owned {
    let marshalled = children.iter().map(|child| marshal(child, hold)).collect();
    build_runtime_slist(marshalled)
}

// ---------------------------------------------------------------------------
// Low-level allocation helpers
// ---------------------------------------------------------------------------

enum StoredField {
    Scalar(i64),
    Owned(Owned),
}

/// Allocate a Sexp cell with one field: `[header | tag | field]`.
fn alloc_sexp_cell(tag: i64, field: StoredField) -> Owned {
    let base = cranelisp_intrinsics::alloc::heap_alloc(HeapAdt::payload_size(1) as i64);
    // SAFETY: base is a valid heap pointer with payload space for a tag and
    // one field.
    unsafe {
        write_i64(base, TAG_OFFSET, tag);
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
    let base = cranelisp_intrinsics::alloc::heap_alloc(HeapAdt::payload_size(2) as i64);
    // SAFETY: base is a valid heap pointer with payload space for a tag and
    // two fields.
    unsafe {
        write_i64(base, TAG_OFFSET, tag);
        write_i64(base, FIELD0_OFFSET, field0.into_raw());
        write_i64(base, FIELD1_OFFSET, field1.into_raw());
    }
    // SAFETY: the fresh allocation is fully initialized at RC=1.
    unsafe { Owned::from_abi(base) }
}

/// Allocate an SCons cell: `[header | tag=1 | head | tail]`.
fn alloc_scons(head: Owned, tail: Owned) -> Owned {
    let base = cranelisp_intrinsics::alloc::heap_alloc(HeapAdt::payload_size(2) as i64);
    // SAFETY: base is a valid heap pointer with payload space for a tag, the
    // head and the tail.
    unsafe {
        write_i64(base, TAG_OFFSET, TAG_SCONS);
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

    fn read_slist_to_vec(slist: Borrowed<'_>) -> Vec<Sexp> {
        Unmarshal {
            caller_names: HashSet::new(),
            caller_text: HashSet::new(),
            span: || Span::SYNTHETIC,
        }
        .read_slist(slist)
    }
    use cranelisp_types::HeapHeader;

    // spec: design/arch/bounded-contexts.md §4b invariant 2 — the marshaller
    // reads and writes Sexp cells at the layout owner's offsets
    #[test]
    fn cell_offsets_are_the_heap_adt_layout() {
        assert_eq!(TAG_OFFSET, HeapAdt::TAG_OFFSET as usize);
        assert_eq!(FIELD0_OFFSET, HeapAdt::field_offset(0) as usize);
        assert_eq!(FIELD1_OFFSET, HeapAdt::field_offset(1) as usize);
    }

    // spec: design/arch/bounded-contexts.md §4b invariant 2 — a marshalled
    // cell, read through the owner's layout alone, carries its size, tag and
    // fields where `HeapAdt` places them
    #[test]
    fn marshalled_cells_have_the_heap_adt_layout() {
        let word = |base: i64, offset: i32| unsafe { read_i64(base, offset as usize) };
        let alloc_size = |base: i64| word(base, HeapHeader::ALLOC_SIZE_OFFSET);

        let int = sexp_to_runtime(&Sexp::Int(42, Span::SYNTHETIC));
        let base = int.as_borrowed().raw_for_read();
        assert_eq!(
            alloc_size(base),
            (HeapHeader::SIZE + HeapAdt::payload_size(1)) as i64
        );
        assert_eq!(word(base, HeapAdt::TAG_OFFSET), TAG_SEXP_INT);
        assert_eq!(word(base, HeapAdt::field_offset(0)), 42);
        cranelisp_intrinsics::drop::consume_sexp(int);

        let list = sexp_to_runtime(&Sexp::List(
            vec![Sexp::Int(7, Span::SYNTHETIC)],
            Span::SYNTHETIC,
        ));
        let base = list.as_borrowed().raw_for_read();
        assert_eq!(word(base, HeapAdt::TAG_OFFSET), TAG_SEXP_LIST);
        let scons = word(base, HeapAdt::field_offset(0));
        assert_eq!(
            alloc_size(scons),
            (HeapHeader::SIZE + HeapAdt::payload_size(2)) as i64
        );
        assert_eq!(word(scons, HeapAdt::TAG_OFFSET), TAG_SCONS);
        let head = word(scons, HeapAdt::field_offset(0));
        assert_eq!(word(head, HeapAdt::field_offset(0)), 7);
        assert_eq!(word(scons, HeapAdt::field_offset(1)), TAG_SNIL);
        cranelisp_intrinsics::drop::consume_sexp(list);
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
        unsafe { read_i64(base, HeapHeader::RC_OFFSET as usize) }
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
        // SAFETY: `base` is a live Sexp cell with a tag and field 0.
        let tag = unsafe { read_i64(base, TAG_OFFSET) };
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
            // SAFETY: SCons cell with a head and a tail.
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

    // --- E6: the held argument names (expansion-qualification-scope.md §2.7) ---

    fn sym(name: &str) -> Sexp {
        Sexp::Symbol(name.to_string(), Span::SYNTHETIC)
    }

    /// Marshal `(x)` and `(y 1)`-shaped arguments, take a probe reference on
    /// each held name so it stays observable after the turn, and return the
    /// call, the names and their probes.
    fn held_call() -> (ClauseCall, Vec<i64>, Vec<Owned>) {
        let args = [
            sym("x"),
            Sexp::List(
                vec![sym("y"), Sexp::Int(1, Span::SYNTHETIC)],
                Span::SYNTHETIC,
            ),
        ];
        let call = marshal_clause_call(&args);
        let names: Vec<i64> = call.held.0.iter().map(Owned::raw_for_read).collect();
        // SAFETY: each name is live: the argument tree and the hold own it.
        let probes = names
            .iter()
            .map(|&name| unsafe { Borrowed::from_abi(name) }.to_owned())
            .collect();
        (call, names, probes)
    }

    fn release_probes(probes: Vec<Owned>) {
        for probe in probes {
            cranelisp_intrinsics::rc::consume_shallow(probe);
        }
    }

    // spec: design/int/expansion-qualification-scope.md §2.7 E6 — a clause that
    // returns its first argument: during the turn each argument name carries
    // the tree's, the hold's and the probe's references; after it, only the
    // probe's, and the returned name is recorded as caller text.
    #[test]
    fn held_argument_names_are_released_once_on_success() {
        let (call, names, probes) = held_call();
        assert_eq!(names.len(), 2);
        assert_eq!(
            names.iter().map(|&n| cell_rc(n)).collect::<Vec<_>>(),
            [3, 3]
        );

        // The clause: keep the first argument, consume the list.
        // SAFETY: `call.args` is a live SCons whose head is the first argument.
        let first =
            unsafe { Borrowed::from_abi(read_i64(call.args.raw_for_read(), FIELD0_OFFSET)) }
                .to_owned();
        cranelisp_intrinsics::drop::consume_slist(call.args);
        let expansion = take_clause_result(first.into_raw(), call.held).unwrap();

        assert!(matches!(&expansion.sexp, Sexp::Symbol(name, _) if name == "x"));
        let Sexp::Symbol(_, span) = &expansion.sexp else {
            unreachable!("invariant: checked above")
        };
        assert_eq!(expansion.caller_text, HashSet::from([*span]));
        assert_eq!(
            names.iter().map(|&n| cell_rc(n)).collect::<Vec<_>>(),
            [1, 1]
        );
        release_probes(probes);
    }

    // spec: design/int/expansion-qualification-scope.md §2.7 E6 — an invalid
    // result releases the held names too.
    #[test]
    fn held_argument_names_are_released_once_on_an_invalid_result() {
        let (call, names, probes) = held_call();
        cranelisp_intrinsics::drop::consume_slist(call.args);

        let outcome = take_clause_result(TAG_SNIL, call.held);

        assert!(matches!(outcome, Err(InvalidClauseResult(TAG_SNIL))));
        assert_eq!(
            names.iter().map(|&n| cell_rc(n)).collect::<Vec<_>>(),
            [1, 1]
        );
        release_probes(probes);
    }
}
