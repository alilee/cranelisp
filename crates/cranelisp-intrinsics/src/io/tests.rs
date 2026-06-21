use super::*;
use crate::alloc::alloc_with_rc;

/// Helper: allocate a Pure node with the given value.
/// Layout: [header(16) | tag=0(8) | value(8)]
fn make_pure_node(value: i64) -> i64 {
    let base = alloc_with_rc(16); // tag + 1 field = 16 bytes payload
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_PURE;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = value;
    }
    base as i64
}

/// Helper: allocate an Effect node with a pre-built thunk.
/// Layout (ABI v4): [header(16) | tag=1(8) | thunk_ptr(8) |
/// resource_token(8) | fn_name_handle(8)] — 32-byte payload. Field-3 is
/// init to null (the "backend did not stamp" case), so the trampoline's
/// `read_effect_fn_name` degrades to `"<unknown>"`.
fn make_effect_node(result_value: i64) -> i64 {
    make_effect_node_with_name(result_value, 0)
}

/// Helper: allocate an ABI-v4 Effect node, optionally stamping field-3 with
/// a baked fn-name handle (a NUL-terminated C-string pointer, or 0 for the
/// unstamped case).
fn make_effect_node_with_name(result_value: i64, fn_name_handle: i64) -> i64 {
    // Double-box a CLEAN wrapper thunk the way `CLIO::effect*` does post-ABI-v5
    // (FIXME 0327 Option A): the stored thunk returns an `EffectOutcome`.
    let thunk_ptr = clean_effect_thunk(result_value);

    let base = alloc_with_rc(32); // tag + thunk + token + fn_name = 32 bytes (ABI v4)
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_EFFECT;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = thunk_ptr;
        *((base as isize + FIELD_1_OFFSET) as *mut i64) = 0; // resource_token
        *((base as isize + FIELD_2_OFFSET) as *mut i64) = fn_name_handle;
    }
    base as i64
}

/// Build a CLEAN wrapper thunk returning `EffectOutcome { value, null, 0 }`,
/// matching `CLIO::effect*`'s ABI-v5 stored-thunk shape. Returns the
/// double-boxed thunk pointer (consumed once by `call_effect_thunk`).
fn clean_effect_thunk(value: i64) -> i64 {
    let thunk: Box<Box<dyn FnOnce() -> cranelisp_platform::EffectOutcome>> =
        Box::new(Box::new(move || cranelisp_platform::EffectOutcome {
            value,
            fault_cause: std::ptr::null(),
            fault_len: 0,
        }));
    Box::into_raw(thunk) as i64
}

/// Build a FAULTING wrapper thunk returning an `EffectOutcome` with a
/// non-null `fault_cause` carrying `cause`, modelling what the DLL-local
/// `catch_unwind` in `CLIO::effect*` produces when the user closure panics.
/// The cause bytes are leaked (session-bounded), mirroring the DLL wrapper's
/// `String::leak`. Returns the double-boxed thunk pointer.
fn faulting_effect_thunk(cause: &'static str) -> i64 {
    let thunk: Box<Box<dyn FnOnce() -> cranelisp_platform::EffectOutcome>> =
        Box::new(Box::new(move || cranelisp_platform::EffectOutcome {
            value: 0,
            fault_cause: cause.as_ptr(),
            fault_len: cause.len(),
        }));
    Box::into_raw(thunk) as i64
}

/// Helper: allocate a Bind node linking inner IO to a continuation.
/// Layout: [header(16) | tag=2(8) | inner_io(8) | cont(8)]
fn make_bind_node(inner: i64, cont: i64) -> i64 {
    let base = alloc_with_rc(24); // tag + inner + cont = 24 bytes
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_BIND;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = inner;
        *((base as isize + FIELD_1_OFFSET) as *mut i64) = cont;
    }
    base as i64
}

/// Helper: allocate a minimal "closure" that returns a Pure node wrapping
/// the argument value + an offset.
///
/// This simulates `(fn [x] (Pure (+ x offset)))`.
/// The closure env stores the offset as a capture at offset 32.
fn make_add_and_pure_closure(offset: i64) -> i64 {
    // The closure's code function: reads offset from env, adds to val,
    // wraps in Pure.
    extern "C" fn add_and_pure(env_ptr: i64, val: i64) -> i64 {
        let offset = unsafe { *((env_ptr as isize + 32) as *const i64) };
        make_pure_node_inline(val + offset)
    }

    // Allocate closure: [header(16) | code_ptr(8) | drop_glue_ptr(8) | capture_offset(8)]
    let base = alloc_with_rc(24); // code_ptr + drop_glue_ptr + 1 capture = 24
    unsafe {
        // code_ptr at offset 16
        *((base as isize + 16) as *mut i64) = add_and_pure as *const () as i64;
        // drop_glue_ptr at offset 24 (0 = no captures to drop)
        *((base as isize + 24) as *mut i64) = 0;
        // capture: offset at offset 32
        *((base as isize + 32) as *mut i64) = offset;
    }
    base as i64
}

/// Helper: allocate an identity continuation closure `(fn [x] (Pure x))`.
fn make_identity_pure_closure() -> i64 {
    extern "C" fn identity_pure(_env_ptr: i64, val: i64) -> i64 {
        make_pure_node_inline(val)
    }

    let base = alloc_with_rc(16); // code_ptr + drop_glue_ptr = 16
    unsafe {
        *((base as isize + 16) as *mut i64) = identity_pure as *const () as i64;
        *((base as isize + 24) as *mut i64) = 0;
    }
    base as i64
}

/// Allocate a Pure node — callable from any context including extern "C".
fn make_pure_node_inline(value: i64) -> i64 {
    let base = alloc_with_rc(16);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_PURE;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = value;
    }
    base as i64
}

// spec: 10-io §10.8.1 — Pure node returns value directly
#[test]
fn test_run_io_pure() {
    let io = make_pure_node(42);
    let result = run_io_trampoline(io);
    assert_eq!(result, 42);
}

// spec: 10-io §10.8.1 — Effect node executes thunk and returns result
#[test]
fn test_run_io_effect() {
    let io = make_effect_node(99);
    let result = run_io_trampoline(io);
    assert_eq!(result, 99);
}

// spec: 10-io §10.8.2 — Bind chains are evaluated iteratively (not recursively)
#[test]
fn test_run_io_bind_pure_to_pure() {
    // bind (Pure 10) (fn [x] (Pure (+ x 5)))
    let inner = make_pure_node(10);
    let cont = make_add_and_pure_closure(5);
    let io = make_bind_node(inner, cont);
    let result = run_io_trampoline(io);
    assert_eq!(result, 15);
}

// spec: 10-io §10.8.2 — nested bind chains
#[test]
fn test_run_io_nested_bind() {
    // bind (bind (Pure 1) (fn [x] (Pure (+ x 10)))) (fn [y] (Pure (+ y 100)))
    let inner = make_pure_node(1);
    let cont1 = make_add_and_pure_closure(10);
    let bind1 = make_bind_node(inner, cont1);
    let cont2 = make_add_and_pure_closure(100);
    let io = make_bind_node(bind1, cont2);
    let result = run_io_trampoline(io);
    assert_eq!(result, 111);
}

// spec: 10-io §10.8.2 — bind with Effect evaluates the thunk
#[test]
fn test_run_io_bind_effect() {
    // bind (Effect -> 7) (fn [x] (Pure (+ x 3)))
    let inner = make_effect_node(7);
    let cont = make_add_and_pure_closure(3);
    let io = make_bind_node(inner, cont);
    let result = run_io_trampoline(io);
    assert_eq!(result, 10);
}

// spec: 10-io §10.8.2 — deep bind chain runs without stack overflow (O(1) call stack)
#[test]
fn test_run_io_deep_bind_chain() {
    // Build a chain of 1000 binds: bind (bind (... (Pure 0) ...) (+1)) (+1)
    // Result should be 1000.
    let mut io = make_pure_node(0);
    for _ in 0..1000 {
        let cont = make_add_and_pure_closure(1);
        io = make_bind_node(io, cont);
    }
    let result = run_io_trampoline(io);
    assert_eq!(result, 1000);
}

// spec: 10-io §10.8.2 — bind with identity continuation
#[test]
fn test_run_io_bind_identity() {
    // bind (Pure 42) (fn [x] (Pure x))
    let inner = make_pure_node(42);
    let cont = make_identity_pure_closure();
    let io = make_bind_node(inner, cont);
    let result = run_io_trampoline(io);
    assert_eq!(result, 42);
}

// spec: 10-io §10.8.1 — unknown IO tag panics
#[test]
#[should_panic(expected = "unknown IO tag")]
fn test_run_io_unknown_tag_panics() {
    // Create a node with an invalid tag.
    // Call run_io_trampoline (not the extern "C" wrapper) so panic can unwind.
    let base = alloc_with_rc(16);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = 99; // invalid tag
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = 0;
    }
    run_io_trampoline(base as i64);
}

// --- Par node tests ---

/// Helper: allocate a Par node with the given branch IO pointers.
/// Layout: [header(16) | tag=3(8) | count(8) | branch_0(8) | branch_1(8) | ...]
fn make_par_node(branches: &[i64]) -> i64 {
    let payload_size = 8 + 8 + branches.len() * 8; // tag + count + N branches
    let base = alloc_with_rc(payload_size);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_PAR;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = branches.len() as i64;
        for (i, &branch) in branches.iter().enumerate() {
            *((base as isize + FIELD_1_OFFSET + (i as isize) * 8) as *mut i64) = branch;
        }
    }
    base as i64
}

/// Helper: allocate a continuation that reads N results from a results_ptr
/// (an alloc_with_rc buffer) and returns a Pure node wrapping their sum.
fn make_sum_results_closure(count: usize) -> i64 {
    extern "C" fn sum_results(env_ptr: i64, results_ptr: i64) -> i64 {
        let count = unsafe { *((env_ptr as isize + 32) as *const i64) } as usize;
        let mut sum = 0i64;
        for i in 0..count {
            // Results are at FIELD_0_OFFSET + i*8 (offsets 24, 32, 40, ...)
            sum += unsafe {
                *((results_ptr as isize + FIELD_0_OFFSET + (i as isize) * 8) as *const i64)
            };
        }
        // Dec the results buffer (alloc_with_rc allocation, rc=1).
        // Dealloc directly since the test continuation is the sole owner.
        crate::alloc::heap_dealloc(results_ptr);
        make_pure_node_inline(sum)
    }

    let base = alloc_with_rc(24); // code_ptr + drop_glue_ptr + 1 capture
    unsafe {
        *((base as isize + 16) as *mut i64) = sum_results as *const () as i64;
        *((base as isize + 24) as *mut i64) = 0;
        *((base as isize + 32) as *mut i64) = count as i64;
    }
    base as i64
}

// spec: 10-io §10.12 — Par node dispatches branches and collects results
#[test]
fn test_run_io_par_with_bind() {
    // Par [Pure(10), Pure(20)] -> continuation sums results -> Pure(30)
    let b0 = make_pure_node(10);
    let b1 = make_pure_node(20);
    let par = make_par_node(&[b0, b1]);
    let cont = make_sum_results_closure(2);
    let io = make_bind_node(par, cont);
    let result = run_io_trampoline(io);
    assert_eq!(result, 30);
}

// spec: 10-io §10.12 — Par with three branches
#[test]
fn test_run_io_par_three_branches() {
    let b0 = make_pure_node(100);
    let b1 = make_pure_node(200);
    let b2 = make_pure_node(300);
    let par = make_par_node(&[b0, b1, b2]);
    let cont = make_sum_results_closure(3);
    let io = make_bind_node(par, cont);
    let result = run_io_trampoline(io);
    assert_eq!(result, 600);
}

// spec: 10-io §10.12.4 — resource token serialization preserves ordering
#[test]
fn test_run_io_par_with_effects() {
    use std::sync::{Arc, Mutex};

    // Create Effect nodes with different resource tokens.
    // Two effects share token=1 (must run sequentially).
    // One effect has token=0 (independent).
    let order = Arc::new(Mutex::new(Vec::new()));

    let order_clone = order.clone();
    let make_tracking_effect = |id: i64, token: i64| -> i64 {
        let order = order_clone.clone();
        // Wrapper thunk returning a clean EffectOutcome (ABI v5), preserving
        // the ordering side effect.
        let thunk: Box<Box<dyn FnOnce() -> cranelisp_platform::EffectOutcome>> =
            Box::new(Box::new(move || {
                order.lock().unwrap().push(id);
                cranelisp_platform::EffectOutcome {
                    value: id,
                    fault_cause: std::ptr::null(),
                    fault_len: 0,
                }
            }));
        let thunk_ptr = Box::into_raw(thunk) as i64;

        let base = alloc_with_rc(32); // ABI v4: + fn_name_handle field-3
        unsafe {
            *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_EFFECT;
            *((base as isize + FIELD_0_OFFSET) as *mut i64) = thunk_ptr;
            *((base as isize + FIELD_1_OFFSET) as *mut i64) = token;
            *((base as isize + FIELD_2_OFFSET) as *mut i64) = 0; // fn_name: unstamped
        }
        base as i64
    };

    let e0 = make_tracking_effect(1, 0);  // token=0, independent
    let e1 = make_tracking_effect(2, 1);  // token=1, serial group
    let e2 = make_tracking_effect(3, 1);  // token=1, serial group

    let par = make_par_node(&[e0, e1, e2]);
    let cont = make_sum_results_closure(3);
    let io = make_bind_node(par, cont);
    let result = run_io_trampoline(io);

    // Results should be placed in original order regardless of dispatch order.
    assert_eq!(result, 6); // 1 + 2 + 3

    // Token=1 effects should have run sequentially (2 before 3).
    let executed = order.lock().unwrap();
    let pos_2 = executed.iter().position(|&x| x == 2).unwrap();
    let pos_3 = executed.iter().position(|&x| x == 3).unwrap();
    assert!(pos_2 < pos_3, "Token=1 effects should run in order: {executed:?}");
}

// ---------------------------------------------------------------------
// Decision 24 + Decision 29 extern-consumption tests (Sprint 56 Step 2c,
// Sprint 57 Wave 3).
//
// `cranelisp_run_io` runs the trampoline, which owns RC balance for the
// full IO tree: every intermediate Pure/Effect/Bind/Par node (including
// the top-level root) is shallow-dec'd inline via `drop::dec_shallow_io`,
// and every continuation closure is `drop::consume_closure`-dec'd after
// invocation. The following tests assert alloc_count == dealloc_count
// on balanced programs of varying shape.
// ---------------------------------------------------------------------

// spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern cranelisp_run_io
#[test]
fn decision24_run_io_pure_rc_balanced() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();

    // Pure(42): trampoline returns 42 (scalar — no heap ownership to
    // track). run_io_trampoline shallow-dec's the Pure node on the
    // no-continuation return path.
    let pure = make_pure_node(42);
    let result = cranelisp_run_io(pure);
    assert_eq!(result, 42);

    // allocs: 1 Pure node. deallocs: 1 (trampoline shallow-dec on return).
    assert_eq!(
        crate::alloc::alloc_count() - allocs_before,
        1,
        "alloc count mismatch"
    );
    assert_eq!(
        crate::alloc::dealloc_count() - deallocs_before,
        1,
        "dealloc count mismatch (leak or double-free)"
    );
}

// spec: design/arch/CLAUDE.md Decision 29 — trampoline inline-dec's every
// intermediate node (Pure + Bind + continuation) and the final Pure.
#[test]
fn run_io_trampoline_rc_balanced() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();

    // bind (Pure 10) (fn [x] (Pure (+ x 5)))
    //   allocations:
    //     1. inner Pure(10)
    //     2. continuation closure (add_and_pure w/ offset=5)
    //     3. Bind node
    //     4. Pure(15) produced by the continuation
    //   deallocations (post-fix):
    //     1. Bind shallow-dec after its inner/cont are transferred out
    //     2. inner Pure shallow-dec before calling the continuation
    //     3. continuation closure via consume_closure (no captures → bare
    //        closure, drop_glue_ptr=0)
    //     4. result Pure(15) shallow-dec on the final return path
    let inner = make_pure_node(10);
    let cont = make_add_and_pure_closure(5);
    let io = make_bind_node(inner, cont);

    let result = cranelisp_run_io(io);
    assert_eq!(result, 15);

    assert_eq!(
        crate::alloc::alloc_count() - allocs_before,
        4,
        "expected 4 allocations (inner + cont + bind + continuation-produced Pure)"
    );
    assert_eq!(
        crate::alloc::dealloc_count() - deallocs_before,
        4,
        "expected 4 deallocations (alloc_count == dealloc_count invariant)"
    );
}

// spec: design/arch/CLAUDE.md Decision 29 — deep bind chain is RC-balanced
// (was the O(N) leak reason before Wave 3).
#[test]
fn run_io_trampoline_deep_bind_chain_rc_balanced() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();

    // 100-deep bind chain: Pure(0) → +1 → +1 → ... → 100
    //   allocations per step: 1 Bind + 1 continuation closure = 2
    //   plus the leading Pure(0) and per-continuation Pure result
    //   total: 1 (initial Pure) + N * (Bind + cont + result Pure) = 1 + 3N
    let mut io = make_pure_node(0);
    for _ in 0..100 {
        let cont = make_add_and_pure_closure(1);
        io = make_bind_node(io, cont);
    }
    let result = cranelisp_run_io(io);
    assert_eq!(result, 100);

    let allocs = crate::alloc::alloc_count() - allocs_before;
    let deallocs = crate::alloc::dealloc_count() - deallocs_before;
    assert_eq!(
        allocs, deallocs,
        "deep bind chain must be RC-balanced: {allocs} allocs vs {deallocs} deallocs"
    );
}

// spec: design/arch/CLAUDE.md Decision 29 — call_continuation dec's the
// closure when `cont_is_fresh=true` (closure belonged to a fresh/
// continuation-produced Bind). Closures from the caller's tree
// (`cont_is_fresh=false`) are left alone for post-return consume_io_tree.
#[test]
fn call_continuation_dec_closure() {
    use std::sync::atomic::AtomicI64;

    // Case A: cont_is_fresh=true — closure is consumed post-call.
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();

    let cont = make_identity_pure_closure();
    let rc_before = unsafe {
        let rc_ptr =
            &*((cont as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64);
        rc_ptr.load(std::sync::atomic::Ordering::Acquire)
    };
    assert_eq!(rc_before, 1, "fresh closure starts at rc=1");

    let result_io = call_continuation(cont, 42, true);
    assert_eq!(
        crate::alloc::dealloc_count() - deallocs_before,
        1,
        "call_continuation with cont_is_fresh=true must consume the closure"
    );
    assert_eq!(
        crate::alloc::alloc_count() - allocs_before,
        2,
        "2 allocs: closure + continuation-produced Pure"
    );

    // Clean up the returned Pure.
    crate::drop::dec_shallow_io(result_io);
    assert_eq!(crate::alloc::dealloc_count() - deallocs_before, 2);

    // Case B: cont_is_fresh=false — closure stays live.
    let allocs_b_before = crate::alloc::alloc_count();
    let deallocs_b_before = crate::alloc::dealloc_count();

    let cont_b = make_identity_pure_closure();
    let result_b = call_continuation(cont_b, 7, false);
    assert_eq!(
        crate::alloc::dealloc_count() - deallocs_b_before,
        0,
        "call_continuation with cont_is_fresh=false must NOT consume the closure"
    );
    assert_eq!(
        crate::alloc::alloc_count() - allocs_b_before,
        2,
        "2 allocs: closure + continuation-produced Pure"
    );

    // Clean up manually.
    crate::drop::consume_closure(cont_b);
    crate::drop::dec_shallow_io(result_b);
    assert_eq!(crate::alloc::dealloc_count() - deallocs_b_before, 2);
}

/// Helper: allocate a continuation closure `(fn [x] (runtime_panic …) 0)`
/// that sets the runtime-error slot and returns the panic-path sentinel `0`
/// — modelling the inline div-by-zero codegen (`emit_panic_return`) inside an
/// IO `bind` continuation: it sets the slot then `return_(&[0])` from the
/// enclosing continuation lambda.
fn make_panicking_cont_closure() -> i64 {
    extern "C" fn panic_cont(_env_ptr: i64, _val: i64) -> i64 {
        let msg = "division by zero";
        crate::panic::runtime_panic(msg.as_ptr(), msg.len());
        0 // panic-path sentinel — NOT a valid IO node pointer
    }
    let base = alloc_with_rc(16); // code_ptr + drop_glue_ptr, no captures
    unsafe {
        *((base as isize + 16) as *mut i64) = panic_cont as *const () as i64;
        *((base as isize + 24) as *mut i64) = 0;
    }
    base as i64
}

// spec: spec/12-runtime.md §12.7.4.2 — a runtime panic raised inside an IO
// `bind` continuation makes the continuation return the sentinel `0`. The
// trampoline must PEEK the runtime-error slot, STOP the walk, and return `0`
// WITHOUT dereferencing the sentinel (which would null-deref → SIGSEGV), and
// must LEAVE the slot SET so the host surfaces it (FIXME 0401 — peek, not
// take).
#[test]
fn trampoline_runtime_panic_in_continuation_stops_and_leaves_slot_set() {
    let _ = crate::panic::take_runtime_error(); // clear
    // bind (Pure 1) (fn [_] <panic; return sentinel 0>)
    let inner = make_pure_node(1);
    let cont = make_panicking_cont_closure();
    let io = make_bind_node(inner, cont);

    // Drive the trampoline (NOT the extern wrapper). It must NOT SIGSEGV.
    let result = run_io_trampoline(io);
    assert_eq!(result, 0, "panicking continuation aborts the walk with the sentinel");

    // The slot is left SET — the trampoline peeked, did not take. The host
    // is the surfacing point; if the slot were cleared here the SIGSEGV would
    // be traded for a silent swallow.
    assert!(
        crate::panic::has_runtime_error(),
        "trampoline must leave the runtime-error slot SET for the host"
    );
    // Cleanup: take the slot so it does not pollute later tests on this
    // thread, then release the caller's tree (consume_io_tree walks the
    // Bind/Pure/closure spine the trampoline left untouched on the abort).
    let drained = crate::panic::take_runtime_error();
    assert!(
        drained.as_deref().is_some_and(|m| m.contains("division by zero")),
        "the surfaced message must carry the panic cause (got {drained:?})"
    );
    crate::drop::consume_io_tree(io);
}

// spec: 10-io §10.12 — read_resource_token returns 0 for non-Effect nodes
#[test]
fn test_read_resource_token() {
    let pure = make_pure_node(42);
    assert_eq!(read_resource_token(pure), 0);

    // Effect with token=5 (thunk never forced — only the token is read).
    let effect = {
        let thunk_ptr = clean_effect_thunk(0);
        let base = alloc_with_rc(32); // ABI v4
        unsafe {
            *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_EFFECT;
            *((base as isize + FIELD_0_OFFSET) as *mut i64) = thunk_ptr;
            *((base as isize + FIELD_1_OFFSET) as *mut i64) = 5;
            *((base as isize + FIELD_2_OFFSET) as *mut i64) = 0; // fn_name: unstamped
        }
        base as i64
    };
    assert_eq!(read_resource_token(effect), 5);
}

// -- FIXME 0327 — the fault-guarded platform-dispatch funnel (step 3) --

/// Build a baked fn-name C-string the way the backend would (NUL-terminated
/// UTF-8, program-lifetime). Leaks deliberately — the trampoline reads it by
/// pointer with no length channel and never frees it (mirrors a `.rodata`
/// data symbol). Returns the pointer as an i64 handle for field-3.
fn bake_fn_name(name: &str) -> i64 {
    let cstr = std::ffi::CString::new(name).unwrap();
    std::ffi::CString::into_raw(cstr) as i64
}

// spec: design/arch/bounded-contexts.md §4b invariant 14 — the fault guard
// is a strict no-op on the happy path: a clean thunk forces and returns its
// value, leaving no dispatch fault.
#[test]
fn force_effect_thunk_protected_happy_path_returns_value() {
    let _ = crate::panic::take_dispatch_fault(); // clear
    // Clean wrapper thunk (ABI v5): EffectOutcome with null fault_cause.
    let thunk_ptr = clean_effect_thunk(1234);
    let outcome = unsafe {
        crate::io_guard::force_effect_thunk_protected(thunk_ptr, "stdio/read-line")
    };
    match outcome {
        crate::io_guard::ForceOutcome::Value(v) => assert_eq!(v, 1234),
        crate::io_guard::ForceOutcome::Faulted => panic!("clean thunk must not fault"),
    }
    assert!(
        crate::panic::take_dispatch_fault().is_none(),
        "no dispatch fault on the happy path"
    );
}

// spec: design/arch/bounded-contexts.md §4b invariant 14 — a faulted
// EffectOutcome (FIXME 0327 Option A: the panic was caught DLL-side and a
// non-null fault_cause returned) produces a Faulted outcome whose captured
// dispatch fault carries the supplied fn-name and the cause string read from
// the EffectOutcome C-string.
#[test]
fn force_effect_thunk_protected_faulted_outcome_captures_fn_name() {
    let _ = crate::panic::take_dispatch_fault();
    let _ = crate::panic::take_runtime_error();
    // The DLL-local catch already converted the panic into an EffectOutcome
    // carrying the cause; the guard reads it (no host-side catch_unwind).
    let thunk_ptr = faulting_effect_thunk("device unavailable");
    let outcome = unsafe {
        crate::io_guard::force_effect_thunk_protected(thunk_ptr, "stdio/read-line")
    };
    assert!(
        matches!(outcome, crate::io_guard::ForceOutcome::Faulted),
        "faulted EffectOutcome must fault"
    );
    let fault = crate::panic::take_dispatch_fault().expect("fault captured");
    assert_eq!(fault.fn_name, "stdio/read-line");
    assert!(
        fault.cause.contains("device unavailable"),
        "cause must carry the EffectOutcome message, got {:?}",
        fault.cause
    );
}

// spec: design/arch/bounded-contexts.md §4b invariant 14 — a Rust panic in
// foreign platform code is caught DLL-side, returned as a non-null
// fault_cause, and the guard composes a DispatchFault from it.
#[test]
fn force_effect_thunk_protected_dll_caught_panic_is_read() {
    let _ = crate::panic::take_dispatch_fault();
    let _ = crate::panic::take_runtime_error();
    let thunk_ptr = faulting_effect_thunk("boom in platform fn");
    let outcome = unsafe {
        crate::io_guard::force_effect_thunk_protected(thunk_ptr, "net/connect")
    };
    assert!(
        matches!(outcome, crate::io_guard::ForceOutcome::Faulted),
        "DLL-caught panic must surface as a fault"
    );
    let fault = crate::panic::take_dispatch_fault().expect("fault captured");
    assert_eq!(fault.fn_name, "net/connect");
    assert!(fault.cause.contains("boom in platform fn"));
}

// spec: design/arch/bounded-contexts.md §5 invariant 9 — the trampoline
// reads the baked fn-name from the Effect node's field-3 (ABI v4) and the
// captured fault carries it. The full-trampoline path exercises the
// field-3 read alongside the force.
#[test]
fn trampoline_effect_fault_reads_baked_fn_name() {
    let _ = crate::panic::take_dispatch_fault();
    let _ = crate::panic::take_runtime_error();
    // Build an Effect node whose forced thunk yields a faulted EffectOutcome
    // (modelling the DLL-local catch), with field-3 stamped to a baked
    // fn-name the way the backend would.
    let handle = bake_fn_name("clock/now");
    let thunk_ptr = faulting_effect_thunk("clock read failed");
    let base = alloc_with_rc(32);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_EFFECT;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = thunk_ptr;
        *((base as isize + FIELD_1_OFFSET) as *mut i64) = 0;
        *((base as isize + FIELD_2_OFFSET) as *mut i64) = handle;
    }
    // Drive the trampoline; the EFFECT arm faults and returns the sentinel.
    let result = run_io_trampoline(base as i64);
    assert_eq!(result, 0, "faulting trampoline returns the sentinel");
    let fault = crate::panic::take_dispatch_fault().expect("fault captured");
    assert_eq!(fault.fn_name, "clock/now", "field-3 fn-name read");
    assert!(fault.cause.contains("clock read failed"));
    unsafe { crate::alloc::dealloc(base) };
}

// spec: design/arch/bounded-contexts.md §5 invariant 9 — a node the backend
// did NOT stamp (field-3 null) degrades the captured fn-name to
// "<unknown>", never crashing.
#[test]
fn trampoline_effect_fault_null_fn_name_degrades_to_unknown() {
    let _ = crate::panic::take_dispatch_fault();
    let _ = crate::panic::take_runtime_error();
    // make_effect_node leaves field-3 null, but its thunk is clean; build a
    // faulting one (faulted EffectOutcome) with a null field-3 directly.
    let thunk_ptr = faulting_effect_thunk("unstamped fault");
    let base = alloc_with_rc(32);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_EFFECT;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = thunk_ptr;
        *((base as isize + FIELD_1_OFFSET) as *mut i64) = 0;
        *((base as isize + FIELD_2_OFFSET) as *mut i64) = 0; // unstamped
    }
    let result = run_io_trampoline(base as i64);
    assert_eq!(result, 0);
    let fault = crate::panic::take_dispatch_fault().expect("fault captured");
    assert_eq!(fault.fn_name, "<unknown>", "null field-3 degrades to <unknown>");
    assert!(fault.cause.contains("unstamped fault"));
    unsafe { crate::alloc::dealloc(base) };
}

// spec: design/arch/bounded-contexts.md §4b invariant 14 — the existing
// clean Effect path through the trampoline still works (no fault) after the
// guard is installed: the happy path is unaffected (read_effect_fn_name on a
// clean node leaves no fault).
#[test]
fn trampoline_clean_effect_leaves_no_fault() {
    let _ = crate::panic::take_dispatch_fault();
    let io = make_effect_node_with_name(77, bake_fn_name("stdio/write"));
    let result = run_io_trampoline(io);
    assert_eq!(result, 77);
    assert!(
        crate::panic::take_dispatch_fault().is_none(),
        "clean effect must leave no dispatch fault"
    );
    unsafe { crate::alloc::dealloc(io as *mut u8) };
}
