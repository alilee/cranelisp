use super::*;
use crate::alloc::{alloc_count, alloc_with_rc, dealloc_count};
use crate::heap_string::alloc_string;
use cranelisp_types::TAG_SCONS;

// Helpers -----------------------------------------------------------------

fn alloc_slot(payload: usize) -> i64 {
    alloc_with_rc(payload) as i64
}

/// Write a field through the single mechanical owner (0850) — the fixtures use
/// the same accessor the production drop glue does.
fn write_field(base: i64, offset: isize, value: i64) {
    // SAFETY: `base` is a live fixture allocation with `offset + 8` bytes.
    unsafe { crate::heap_access::write_i64(base, offset, value) }
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
    write_field(base, crate::vec_runtime::LEN_OFFSET as isize, 0);
    write_field(base, crate::vec_runtime::CAP_OFFSET as isize, cap);
    // Allocate through the tracked path (Principle 7 / Principle 22): a raw
    // `alloc_zeroed` here would bypass `databuf_guard::on_alloc`, so the guard's
    // "NOT live" tripwire in `consume_vec_with` would fire on a never-registered
    // buffer. `consume_vec_with` frees via `free_data_buffer`, closing the pair.
    let data: *mut i64 = crate::vec_runtime::alloc_data_buffer(cap);
    write_field(base, crate::vec_runtime::DATA_PTR_OFFSET as isize, data as i64);
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
        let rc_ptr = &*((sym as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64);
        rc_ptr.fetch_add(1, Ordering::Release);
    }

    consume_sexp(sym); // dec rc to 1 — must NOT free

    assert_eq!(alloc_count() - allocs, 2);
    assert_eq!(
        dealloc_count() - deallocs,
        0,
        "shared ref must not be freed"
    );

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
    write_field(vec, crate::vec_runtime::LEN_OFFSET as isize, 3);

    consume_vec_of_string(vec);
    assert_eq!(alloc_count() - allocs, 4); // vec struct + 3 strings
    assert_eq!(dealloc_count() - deallocs, 4);
}

// spec: design/arch/principles/22-published-pointers-have-retention-owners.md —
// the databuf guard's freed-buffer tripwire must stay armed for fixture-built
// vecs: after the product consume path frees the data buffer (via
// `free_data_buffer` → `databuf_guard::on_free`), touching the stale pointer
// fires "NOT live". Pins that routing `make_vec_struct` through the tracked
// `alloc_data_buffer` registers AND releases — the guard is not neutered.
// Deterministic: `assert_live` only reads, and nothing re-allocates the address
// between the consume and the assert.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "NOT live")]
fn databuf_guard_still_trips_on_stale_fixture_buffer_after_consume() {
    let (vec, data) = make_vec_struct(2);
    // len stays 0 — no elements to walk; consume frees the data buffer + struct.
    consume_vec_of_string(vec);
    // The buffer is now deregistered (FREED). A stale touch must trip the guard.
    crate::vec_runtime::debug_assert_live_buffer(data, 2, "test(stale-fixture)");
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
    write_field(vec, crate::vec_runtime::LEN_OFFSET as isize, 2);

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

// spec: design/backend/ring2-rc.md §3.5.10 — FIXME 0474: the FRESH-node release
// path `dec_shallow_io` on a last-ref IO_TAG_SELECT (= 6) node must DEEP-free the
// field-0 branch carrier Vec + every branch IO sub-tree (a fresh select node — one
// a bind continuation built — is released here, NOT via consume_io_tree). RED on
// revert: a bare shallow dec frees only the node header → the Vec + both branches
// leak (the 0474 fresh-continuation-produced branch-Vec leak).
#[test]
fn dec_shallow_io_select_deep_frees_branch_vec_and_all_branches() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    // Two Pure branches.
    let b0 = alloc_slot(16);
    write_field(b0, TAG_OFFSET, IO_TAG_PURE);
    write_field(b0, FIELD0_OFFSET, 42);
    let b1 = alloc_slot(16);
    write_field(b1, TAG_OFFSET, IO_TAG_PURE);
    write_field(b1, FIELD0_OFFSET, 7);

    // Branch carrier Vec [b0, b1].
    let (vec, data) = make_vec_struct(2);
    unsafe {
        *data.add(0) = b0;
        *data.add(1) = b1;
    }
    write_field(vec, crate::vec_runtime::LEN_OFFSET as isize, 2);

    // Fresh IO_TAG_SELECT (= 6) node: tag + field-0 = the Vec.
    let node = alloc_slot(16);
    write_field(node, TAG_OFFSET, 6); // IO_TAG_SELECT
    write_field(node, FIELD0_OFFSET, vec);

    dec_shallow_io(node);

    // node + vec struct + b0 + b1 = 4 alloc_with_rc-tracked allocations, all freed.
    assert_eq!(alloc_count() - allocs, 4);
    assert_eq!(
        dealloc_count() - deallocs,
        4,
        "dec_shallow_io on a fresh SELECT node must deep-free the branch Vec and \
         BOTH branches (FIXME 0474) — a shallow dec would leak the Vec + branches"
    );
}

// spec: design/backend/ring2-rc.md §3.5.10 — FIXME 0474: the same deep-free for a
// fresh IO_TAG_PAR (= 3) node. `dec_shallow_io` must walk the field0=count /
// FIELD1+i*8 branches and free each. RED on revert: shallow dec leaks both branches.
#[test]
fn dec_shallow_io_par_deep_frees_branches() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    let b0 = alloc_slot(16);
    write_field(b0, TAG_OFFSET, IO_TAG_PURE);
    write_field(b0, FIELD0_OFFSET, 1);
    let b1 = alloc_slot(16);
    write_field(b1, TAG_OFFSET, IO_TAG_PURE);
    write_field(b1, FIELD0_OFFSET, 2);

    // Fresh IO_TAG_PAR node: tag + count + 2 branch pointers.
    let par = alloc_slot(32);
    write_field(par, TAG_OFFSET, IO_TAG_PAR);
    write_field(par, FIELD0_OFFSET, 2); // count
    write_field(par, FIELD1_OFFSET, b0);
    write_field(par, FIELD1_OFFSET + 8, b1);

    dec_shallow_io(par);

    assert_eq!(alloc_count() - allocs, 3);
    assert_eq!(
        dealloc_count() - deallocs,
        3,
        "dec_shallow_io on a fresh PAR node must deep-free both branches (FIXME 0474)"
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
        let rc_ptr =
            &*((node as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64);
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

// spec: design/runtime/s118-structural-embedding-ownership.md §2 RE-2 —
// `consume_*` are TREE-OWNERSHIP drop glue and stay so. The S118 W2b ruling
// fixed the producer (`marshal::sconcat`'s tail embed) and left this consumer
// untouched; deep-consume was rejected because it would tear down genuinely
// shared tails.
//
// The fence: `a = [x, y]`; `b = SCons(z, a)` takes its own reference to `a`.
// Releasing `b` must descend only as far as the first node that is NOT on its
// last reference — `a` — and stop there, leaving `a` readable. A change that
// made `consume_slist` descend past a live reference fails here.
#[test]
fn re2_consume_slist_stops_at_a_live_interior_reference() {
    let allocs = alloc_count();
    let deallocs = dealloc_count();

    let x = make_sexp_sym(alloc_string(b"x") as i64);
    let y = make_sexp_sym(alloc_string(b"y") as i64);
    let z = make_sexp_sym(alloc_string(b"z") as i64);
    let a = make_scons(x, make_scons(y, 0));
    // `b` embeds `a` structurally: exactly ONE inc on the node it stores
    // (RE-1, the producer rule this consumer is the dual of).
    crate::rc::rc_inc(a);
    let b = make_scons(z, a);

    consume_slist(b);

    // `a` is still on a live reference and must be intact.
    // SAFETY: `a` is still owned by this frame — `consume_slist(b)` released
    // only `b`'s reference to it (rc 2 -> 1).
    unsafe {
        assert_eq!(
            crate::heap_access::read_i64(a, HeapHeader::RC_OFFSET as isize),
            1,
            "RE-2: b's release must dec a's rc by exactly one, not free it"
        );
        assert_eq!(
            crate::heap_access::read_i64(a, FIELD0_OFFSET),
            x,
            "the shared tail must still read correctly after b's release"
        );
    }
    // b's own node + z + z's string: three frees, and nothing from `a`.
    assert_eq!(
        dealloc_count() - deallocs,
        3,
        "RE-2: the walk stops at the first node not on its last reference"
    );

    consume_slist(a);
    assert_eq!(
        alloc_count() - allocs,
        dealloc_count() - deallocs,
        "both releases together balance exactly (no leak, no double-free)"
    );
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

// ---------------------------------------------------------------------------
// 0850 — single-owner convergence (design §9.1–§9.3, §10 heap_access row)
// ---------------------------------------------------------------------------

// GREP-ZERO: `drop.rs` carries no local raw reader and no copy of the Vec layout
// offsets. `heap_access::{read_i64, write_i64}` is the single mechanical owner
// and `vec_runtime` the single Vec-layout authority — the crate's `CLAUDE.md`
// has declared both for three sprints while the source contradicted it (the
// third-sprint recurrence of S87 F3). This row makes the guidance true and keeps
// it true: a re-introduced private reader or offset copy fails HERE, at the
// seam, not in a later audit.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §9.1–§9.2, §10 grep-zero row)
#[test]
fn drop_module_declares_no_local_reader_or_layout_copy() {
    let src = include_str!("../drop.rs");
    assert!(
        !src.contains("unsafe fn read_i64"),
        "drop.rs must not define a private raw reader — heap_access owns it"
    );
    assert!(
        !src.contains("fn write_i64"),
        "drop.rs must not define a private raw writer — heap_access owns it"
    );
    for copy in ["VEC_LEN_OFFSET", "VEC_CAP_OFFSET", "VEC_DATA_PTR_OFFSET"] {
        assert!(
            !src.contains(copy),
            "drop.rs must not copy {copy} — vec_runtime is the layout authority"
        );
    }
    // The ADT field geometry stays here (it is not Vec layout) but must DERIVE
    // from the header-layout authority rather than restating the header size.
    assert!(
        src.contains("const TAG_OFFSET: isize = HeapHeader::SIZE as isize;"),
        "TAG_OFFSET must derive from HeapHeader::SIZE"
    );
}

// The offsets this module reads with are the authorities' values — a derivation
// that drifted would be caught here rather than by a wrong heap read.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §9.1–§9.3)
#[test]
fn derived_offsets_equal_their_layout_authorities() {
    assert_eq!(TAG_OFFSET, HeapHeader::SIZE as isize);
    assert_eq!(FIELD0_OFFSET, TAG_OFFSET + 8);
    assert_eq!(FIELD1_OFFSET, TAG_OFFSET + 16);
    // The closure drop-glue slot: ONE home, imported by `ivar.rs` (§9.3 fold —
    // it was byte-identical, so it folded rather than filing).
    assert_eq!(CLOSURE_DROP_GLUE_OFFSET, 24);
    // Vec layout comes from `vec_runtime`, never a local copy.
    assert_eq!(LEN_OFFSET, 16);
    assert_eq!(CAP_OFFSET, 24);
    assert_eq!(DATA_PTR_OFFSET, 32);
}

// A typed round-trip through the shared accessor at the Vec field offsets: the
// three reads `consume_vec_with` performs now go through `heap_access` with
// `vec_runtime`'s constants, and read back exactly what a Vec struct holds.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §10 heap_access/vec_runtime row)
#[test]
fn vec_fields_round_trip_through_the_shared_accessor() {
    let v = alloc_slot(24); // len + cap + data_ptr
    let mut buf = [7i64, 8, 9];
    write_field(v, LEN_OFFSET as isize, 3);
    write_field(v, CAP_OFFSET as isize, 3);
    write_field(v, DATA_PTR_OFFSET as isize, buf.as_mut_ptr() as i64);
    // SAFETY: `v` is a live 40-byte allocation; all three offsets are payload.
    unsafe {
        assert_eq!(crate::heap_access::read_i64(v, LEN_OFFSET as isize), 3);
        assert_eq!(crate::heap_access::read_i64(v, CAP_OFFSET as isize), 3);
        let data = crate::heap_access::read_i64(v, DATA_PTR_OFFSET as isize) as *mut i64;
        assert_eq!(data, buf.as_mut_ptr(), "the data pointer field round-trips");
        assert_eq!(*data.add(2), 9, "and addresses the buffer");
    }
    // Largest field offset this module reads: a PAR node's last branch slot.
    let par = alloc_slot(8 * 8);
    write_field(par, FIELD1_OFFSET + 5 * 8, 0x1234);
    // SAFETY: `par` has 64 payload bytes; FIELD1_OFFSET + 40 is within it.
    unsafe {
        assert_eq!(
            crate::heap_access::read_i64(par, FIELD1_OFFSET + 5 * 8),
            0x1234
        );
    }
    crate::rc::consume_shallow(v);
    crate::rc::consume_shallow(par);
}
