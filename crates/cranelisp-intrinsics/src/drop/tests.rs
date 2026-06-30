use super::*;
use crate::alloc::{alloc_count, alloc_with_rc, dealloc_count};
use crate::heap_string::alloc_string;
use cranelisp_types::TAG_SCONS;

// Helpers -----------------------------------------------------------------

fn alloc_slot(payload: usize) -> i64 {
    alloc_with_rc(payload) as i64
}

fn write_field(base: i64, offset: usize, value: i64) {
    unsafe {
        *((base as *mut u8).add(offset) as *mut i64) = value;
    }
}

fn make_scons(head: i64, tail: i64) -> i64 {
    let base = alloc_slot(24); // tag + head + tail = 24
    write_field(base, TAG_OFFSET, TAG_SCONS);
    write_field(base, FIELD0_OFFSET, head);
    write_field(base, FIELD1_OFFSET, tail);
    base
}

fn make_sexp_str(s_ptr: i64) -> i64 {
    let base = alloc_slot(16); // tag + sval = 16
    write_field(base, TAG_OFFSET, TAG_SEXP_STR);
    write_field(base, FIELD0_OFFSET, s_ptr);
    base
}

fn make_sexp_sym(s_ptr: i64) -> i64 {
    let base = alloc_slot(16);
    write_field(base, TAG_OFFSET, TAG_SEXP_SYM);
    write_field(base, FIELD0_OFFSET, s_ptr);
    base
}

fn make_sexp_list(items: i64) -> i64 {
    let base = alloc_slot(16);
    write_field(base, TAG_OFFSET, TAG_SEXP_LIST);
    write_field(base, FIELD0_OFFSET, items);
    base
}

fn make_vec_struct(cap: i64) -> (i64, *mut i64) {
    let base = alloc_slot(24); // len + cap + data_ptr
    write_field(base, VEC_LEN_OFFSET, 0);
    write_field(base, VEC_CAP_OFFSET, cap);
    let data: *mut i64 = if cap > 0 {
        let byte_size = cap as usize * 8;
        let layout = std::alloc::Layout::from_size_align(byte_size, 8).unwrap();
        unsafe { std::alloc::alloc_zeroed(layout) as *mut i64 }
    } else {
        std::ptr::null_mut()
    };
    write_field(base, VEC_DATA_PTR_OFFSET, data as i64);
    (base, data)
}

// Tests -----------------------------------------------------------------

// spec: design/arch/CLAUDE.md Decision 24 — consume_slist frees a shallow chain
#[test]
fn decision24_consume_slist_frees_chain() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    // Build SCons(SexpInt-style scalar, SCons(SexpInt, SNil)). We use
    // SexpInt because it has no heap sub-refs.
    let int0 = alloc_slot(16);
    write_field(int0, TAG_OFFSET, 0); // TAG_SEXP_INT
    write_field(int0, FIELD0_OFFSET, 10);

    let int1 = alloc_slot(16);
    write_field(int1, TAG_OFFSET, 0);
    write_field(int1, FIELD0_OFFSET, 20);

    let list = make_scons(int0, make_scons(int1, 0));

    consume_slist(list);

    assert_eq!(alloc_count() - allocs, 4); // 2 SCons + 2 SexpInt
    assert_eq!(dealloc_count() - deallocs, 4);
}

// spec: design/arch/CLAUDE.md Decision 24 — consume_sexp frees heap fields
#[test]
fn decision24_consume_sexp_sym_frees_string() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    let name = alloc_string(b"hello") as i64;
    let sym = make_sexp_sym(name);
    consume_sexp(sym);

    assert_eq!(alloc_count() - allocs, 2); // string + sym
    assert_eq!(dealloc_count() - deallocs, 2);
}

// spec: design/arch/CLAUDE.md Decision 24 — consume_sexp of SexpList recurses
#[test]
fn decision24_consume_sexp_list_recurses() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    let s1 = alloc_string(b"foo") as i64;
    let sym1 = make_sexp_sym(s1);
    let s2 = alloc_string(b"bar") as i64;
    let sym2 = make_sexp_str(s2);
    let list = make_scons(sym1, make_scons(sym2, 0));
    let sexp_list = make_sexp_list(list);

    consume_sexp(sexp_list);
    // 2 strings + 2 Sexp wrappers + 2 SCons + 1 SexpList = 7
    assert_eq!(alloc_count() - allocs, 7);
    assert_eq!(dealloc_count() - deallocs, 7);
}

// spec: design/arch/CLAUDE.md Decision 24 — consume_sexp preserves shared refs
#[test]
fn decision24_consume_sexp_preserves_shared_ref() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    let s = alloc_string(b"shared") as i64;
    let sym = make_sexp_sym(s);

    // Simulate a second reference (rc 1 -> 2).
    unsafe {
        let rc_ptr = &*((sym as *const u8).add(HeapHeader::RC_OFFSET as usize)
            as *const AtomicI64);
        rc_ptr.fetch_add(1, Ordering::Release);
    }

    consume_sexp(sym); // dec rc to 1 — must NOT free

    assert_eq!(alloc_count() - allocs, 2);
    assert_eq!(dealloc_count() - deallocs, 0, "shared ref must not be freed");

    // Clean up manually.
    consume_sexp(sym);
    assert_eq!(dealloc_count() - deallocs, 2);
}

// spec: design/arch/CLAUDE.md Decision 24 — consume_vec_of_string frees elements
#[test]
fn decision24_consume_vec_of_string_frees_elements() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    let (vec, data) = make_vec_struct(3);
    unsafe {
        *data = alloc_string(b"a") as i64;
        *data.add(1) = alloc_string(b"b") as i64;
        *data.add(2) = alloc_string(b"c") as i64;
    }
    write_field(vec, VEC_LEN_OFFSET, 3);

    consume_vec_of_string(vec);
    assert_eq!(alloc_count() - allocs, 4); // vec struct + 3 strings
    assert_eq!(dealloc_count() - deallocs, 4);
}

// spec: design/arch/CLAUDE.md Decision 24 — consume_io_tree Pure is scalar
#[test]
fn decision24_consume_io_pure_frees_node() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();
    let base = alloc_slot(16); // tag + payload
    write_field(base, TAG_OFFSET, IO_TAG_PURE);
    write_field(base, FIELD0_OFFSET, 42);
    consume_io_tree(base);
    assert_eq!(alloc_count() - allocs, 1);
    assert_eq!(dealloc_count() - deallocs, 1);
}

// spec: io-trampoline.md §16.5/§16.7 — consume_io_tree on an IO_TAG_SELECT (= 6)
// node dec's the field-0 branch Vec, consuming EVERY branch IO sub-tree (winner +
// losers, exactly once) and freeing the Vec struct + the node. No move-out, no
// null-guard (the contrast with launch). RED on revert: without the `6 =>` arm the
// node falls through to the `_` no-op and only the node is freed → the Vec + both
// branches leak.
#[test]
fn consume_io_select_frees_branch_vec_and_all_branches() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    // Two Pure branches (each an IO_TAG_PURE leaf node).
    let b0 = alloc_slot(16);
    write_field(b0, TAG_OFFSET, IO_TAG_PURE);
    write_field(b0, FIELD0_OFFSET, 42);
    let b1 = alloc_slot(16);
    write_field(b1, TAG_OFFSET, IO_TAG_PURE);
    write_field(b1, FIELD0_OFFSET, 7);

    // The branch carrier Vec [b0, b1].
    let (vec, data) = make_vec_struct(2);
    unsafe {
        *data.add(0) = b0;
        *data.add(1) = b1;
    }
    write_field(vec, VEC_LEN_OFFSET, 2);

    // The IO_TAG_SELECT (= 6) node: tag + field-0 = the Vec.
    let node = alloc_slot(16); // tag + 1 field
    write_field(node, TAG_OFFSET, 6); // IO_TAG_SELECT
    write_field(node, FIELD0_OFFSET, vec);

    consume_io_tree(node);

    // alloc_with_rc-tracked allocations: node + vec struct + b0 + b1 = 4. (The Vec
    // data buffer is a plain allocation, freed by consume_vec_with but not counted.)
    assert_eq!(alloc_count() - allocs, 4);
    assert_eq!(
        dealloc_count() - deallocs,
        4,
        "the select node, its branch Vec, and BOTH branches must be freed exactly once"
    );
}

// spec: design/arch/CLAUDE.md Decision 24 — consume_io_tree Bind recurses
#[test]
fn decision24_consume_io_bind_recurses_into_inner() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    // Inner Pure node.
    let inner = alloc_slot(16);
    write_field(inner, TAG_OFFSET, IO_TAG_PURE);
    write_field(inner, FIELD0_OFFSET, 42);

    // Continuation closure: [header | code_ptr | drop_glue_ptr=0]
    let cont = alloc_slot(16);
    write_field(cont, 16, 0); // code_ptr (not invoked)
    write_field(cont, 24, 0); // drop_glue_ptr = 0

    // Bind node.
    let bind = alloc_slot(24); // tag + inner + cont
    write_field(bind, TAG_OFFSET, IO_TAG_BIND);
    write_field(bind, FIELD0_OFFSET, inner);
    write_field(bind, FIELD1_OFFSET, cont);

    consume_io_tree(bind);
    assert_eq!(alloc_count() - allocs, 3);
    assert_eq!(dealloc_count() - deallocs, 3);
}

// spec: design/arch/CLAUDE.md Decision 24 — consume_io_tree Par dec's each branch
#[test]
fn decision24_consume_io_par_walks_branches() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    // Build two Pure branches.
    let b0 = alloc_slot(16);
    write_field(b0, TAG_OFFSET, IO_TAG_PURE);
    write_field(b0, FIELD0_OFFSET, 1);
    let b1 = alloc_slot(16);
    write_field(b1, TAG_OFFSET, IO_TAG_PURE);
    write_field(b1, FIELD0_OFFSET, 2);

    // Par node: tag + count + 2 branches = 32 bytes payload.
    let par = alloc_slot(32);
    write_field(par, TAG_OFFSET, IO_TAG_PAR);
    write_field(par, FIELD0_OFFSET, 2); // count
    write_field(par, FIELD1_OFFSET, b0);
    write_field(par, FIELD1_OFFSET + 8, b1);

    consume_io_tree(par);
    assert_eq!(alloc_count() - allocs, 3);
    assert_eq!(dealloc_count() - deallocs, 3);
}

// spec: design/arch/CLAUDE.md Decision 24 — consume_closure frees bare closure
#[test]
fn decision24_consume_closure_bare() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();
    // Bare closure: no captures, drop_glue_ptr=0.
    let c = alloc_slot(16); // code_ptr + drop_glue_ptr
    write_field(c, 16, 0);
    write_field(c, 24, 0);
    consume_closure(c);
    assert_eq!(alloc_count() - allocs, 1);
    assert_eq!(dealloc_count() - deallocs, 1);
}

// spec: design/arch/CLAUDE.md Decision 29 — dec_shallow_io frees outer only
#[test]
fn dec_shallow_io_frees_outer_only() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    // Build a Bind node that points at an inner Pure and a continuation
    // closure. `dec_shallow_io` must free ONLY the Bind node, leaving the
    // inner Pure and the continuation untouched (they are the
    // transferred-out subfields, still held by other logical owners).
    let inner = alloc_slot(16);
    write_field(inner, TAG_OFFSET, IO_TAG_PURE);
    write_field(inner, FIELD0_OFFSET, 42);

    let cont = alloc_slot(16);
    write_field(cont, 16, 0); // code_ptr placeholder
    write_field(cont, 24, 0); // drop_glue_ptr = 0

    let bind = alloc_slot(24);
    write_field(bind, TAG_OFFSET, IO_TAG_BIND);
    write_field(bind, FIELD0_OFFSET, inner);
    write_field(bind, FIELD1_OFFSET, cont);

    dec_shallow_io(bind);

    // Exactly one alloc was deallocated (the Bind node); inner + cont are
    // still live and owned by the test.
    assert_eq!(alloc_count() - allocs, 3, "three allocs expected");
    assert_eq!(
        dealloc_count() - deallocs,
        1,
        "dec_shallow_io must not walk fields"
    );

    // Clean up the leftover allocations so the test doesn't leak.
    unsafe {
        alloc::dealloc(inner as *mut u8);
        alloc::dealloc(cont as *mut u8);
    }
    assert_eq!(dealloc_count() - deallocs, 3);
}

// spec: design/arch/CLAUDE.md Decision 29 — dec_shallow_io skips nullary tags
#[test]
fn dec_shallow_io_skips_nullary() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();
    dec_shallow_io(0);
    dec_shallow_io(1);
    dec_shallow_io(NULLARY_THRESHOLD - 1);
    assert_eq!(alloc_count() - allocs, 0);
    assert_eq!(dealloc_count() - deallocs, 0);
}

// spec: design/arch/CLAUDE.md Decision 29 — dec_shallow_io preserves shared refs
#[test]
fn dec_shallow_io_preserves_shared_reference() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    let node = alloc_slot(16);
    write_field(node, TAG_OFFSET, IO_TAG_PURE);
    write_field(node, FIELD0_OFFSET, 99);

    // Simulate a second reference (rc: 1 -> 2).
    unsafe {
        let rc_ptr = &*((node as *const u8).add(HeapHeader::RC_OFFSET as usize)
            as *const AtomicI64);
        rc_ptr.fetch_add(1, Ordering::Release);
    }

    dec_shallow_io(node); // rc: 2 -> 1, no free
    assert_eq!(alloc_count() - allocs, 1);
    assert_eq!(
        dealloc_count() - deallocs,
        0,
        "dec_shallow_io must not free when other refs exist"
    );

    // Clean up the remaining reference.
    dec_shallow_io(node);
    assert_eq!(dealloc_count() - deallocs, 1);
}

// spec: design/arch/CLAUDE.md Decision 24 — nullary tag is a no-op
#[test]
fn decision24_consume_slist_skips_nullary() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();
    consume_slist(0); // SNil
    consume_sexp(0);
    consume_vec_of_string(0);
    consume_io_tree(0);
    consume_closure(0);
    assert_eq!(alloc_count() - allocs, 0);
    assert_eq!(dealloc_count() - deallocs, 0);
}

// design: design/backend/io-trampoline.md §15.5/§15.6 — the null-guarded
// IO_TAG_LAUNCH (=5) field-0 drop. An un-interpreted Launch node (field-0 holds a
// live sub-tree, e.g. an unchosen `if`/`match` arm) frees the sub-tree via the
// guarded recursive consume; a detached one (field-0 == 0 after the trampoline's
// move-out, §15.5) is a no-op on field-0 (the supervised strand owns the sub-tree
// and consumes it — no double-free).
#[test]
fn consume_launch_node_frees_live_subtree() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    // Pure 42 sub-tree (the launched effect, simplest IO leaf): tag + value = 16.
    let sub = alloc_slot(16);
    write_field(sub, TAG_OFFSET, IO_TAG_PURE);
    write_field(sub, FIELD0_OFFSET, 42);

    // IO_TAG_LAUNCH node holding the LIVE sub-tree at field 0: tag + field0 = 16.
    let launch = alloc_slot(16);
    write_field(launch, TAG_OFFSET, cranelisp_platform::IO_TAG_LAUNCH);
    write_field(launch, FIELD0_OFFSET, sub);

    consume_io_tree(launch);
    // Null-guard sees a non-zero field-0 → recurse: BOTH the Launch node and the
    // live sub-tree are freed (no leak).
    assert_eq!(alloc_count() - allocs, 2);
    assert_eq!(dealloc_count() - deallocs, 2);
}

#[test]
fn consume_launch_node_detached_field0_sentinel_is_noop() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    // IO_TAG_LAUNCH node whose field-0 is the `0` sentinel (the trampoline moved
    // the sub-tree into a supervised strand). The null-guard skips field-0; only
    // the node itself is freed — no double-free of the strand-owned sub-tree.
    let launch = alloc_slot(16);
    write_field(launch, TAG_OFFSET, cranelisp_platform::IO_TAG_LAUNCH);
    write_field(launch, FIELD0_OFFSET, 0);

    consume_io_tree(launch);
    assert_eq!(alloc_count() - allocs, 1);
    assert_eq!(dealloc_count() - deallocs, 1);
}
