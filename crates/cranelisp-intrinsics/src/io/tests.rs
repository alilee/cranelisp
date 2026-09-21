use super::*;
use crate::alloc::alloc_with_rc;

/// Helper: allocate a Pure node with the given value.
/// Layout: [header(16) | tag=0(8) | value(8) | payload witness(8)]
fn make_pure_node(value: i64) -> i64 {
    let base = alloc_with_rc(24);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_PURE;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = value;
        *((base as isize + FIELD_1_OFFSET) as *mut i64) = 0;
    }
    base as i64
}

/// An unrestricted [`test_effect_node`].
fn effect_node(value: impl Fn() -> i64 + Send + Sync + 'static) -> i64 {
    test_effect_node(0, 1, value)
}

fn effect_node_on(
    token: i64,
    capacity: i64,
    value: impl Fn() -> i64 + Send + Sync + 'static,
) -> i64 {
    test_effect_node(token, capacity, value)
}

/// An `Effect` node whose thunk returns `value`, with its fn-name field
/// stamped by `fn_name_handle` the way the backend does after the platform call
/// (a NUL-terminated C-string pointer, or 0 for the unstamped case).
fn make_effect_node_with_name(value: i64, fn_name_handle: i64) -> i64 {
    let node = effect_node(move || value);
    // SAFETY: a fresh, unpublished 40-byte `Effect` node; field 2 is the fn-name.
    unsafe { crate::heap_access::write_i64(node, FIELD_2_OFFSET, fn_name_handle) };
    node
}

fn make_effect_node(value: i64) -> i64 {
    make_effect_node_with_name(value, 0)
}

/// An `Effect` node whose closure panics with `cause`. The platform wrapper
/// catches the panic and returns it as a faulted `EffectOutcome`, as it does in
/// a platform DLL.
fn faulting_effect_node(cause: &'static str) -> i64 {
    effect_node(move || -> i64 { panic!("{cause}") })
}

/// The thunk word of an `Effect` node.
fn effect_thunk(node: i64) -> i64 {
    // SAFETY: `node` is a live `Effect` node; field 0 is its thunk.
    unsafe { crate::heap_access::read_i64(node, FIELD_0_OFFSET) }
}

fn release_io(node: i64) {
    crate::drop::consume_io_tree(crate::handle::test_owned(node));
}

static RESULT_DISPOSALS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static FIRST_DISPOSED_VALUE: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(0);
static SECOND_DISPOSED_VALUE: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(0);
static BLOCKING_EFFECT_ENTERED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);
static LATER_SERIAL_EFFECT_RAN: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

extern "C" fn count_result_disposal(_value: i64) {
    RESULT_DISPOSALS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
}

extern "C" fn record_first_disposal(value: i64) {
    FIRST_DISPOSED_VALUE.store(value, std::sync::atomic::Ordering::SeqCst);
    count_result_disposal(value);
}

extern "C" fn record_second_disposal(value: i64) {
    SECOND_DISPOSED_VALUE.store(value, std::sync::atomic::Ordering::SeqCst);
    count_result_disposal(value);
}

// spec: spec/10-io.md §10.12.9 item 4 — a produced value remains owned until
// it is transferred to its continuation/caller. Dropping an armed owner invokes
// its type-directed disposer exactly once; transferring it suppresses disposal.
#[test]
fn produced_value_disposes_on_drop_but_not_after_transfer() {
    RESULT_DISPOSALS.store(0, std::sync::atomic::Ordering::SeqCst);
    {
        let _abandoned =
            ProducedValue::with_disposer(41, ResultDisposer::from_fn(count_result_disposal));
    }
    assert_eq!(
        RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
        1,
        "an abandoned produced value is discharged exactly once"
    );

    let delivered =
        ProducedValue::with_disposer(42, ResultDisposer::from_fn(count_result_disposal)).transfer();
    assert_eq!(delivered, 42);
    assert_eq!(
        RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
        1,
        "transfer moves the ownership obligation to the receiver"
    );
}

// spec: spec/10-io.md §10.12.9 item 4 — a Par buffer owns every initialized
// branch result until the buffer is handed to its continuation.
#[test]
fn abandoned_par_buffer_disposes_every_initialized_slot() {
    RESULT_DISPOSALS.store(0, std::sync::atomic::Ordering::SeqCst);
    FIRST_DISPOSED_VALUE.store(0, std::sync::atomic::Ordering::SeqCst);
    SECOND_DISPOSED_VALUE.store(0, std::sync::atomic::Ordering::SeqCst);
    let deallocs_before = crate::alloc::dealloc_count();
    let buffer = alloc_with_rc(24) as i64;
    unsafe {
        crate::heap_access::write_i64(buffer, FIELD_0_OFFSET, 41);
        crate::heap_access::write_i64(buffer, FIELD_0_OFFSET + 8, 42);
    }
    drop(ProducedValue::par_buffer(
        buffer,
        vec![
            ResultDisposer::from_fn(record_first_disposal),
            ResultDisposer::from_fn(record_second_disposal),
        ],
    ));
    assert_eq!(
        RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
        2,
        "each initialized result is discharged exactly once"
    );
    assert_eq!(
        FIRST_DISPOSED_VALUE.load(std::sync::atomic::Ordering::SeqCst),
        41,
        "slot 0 uses branch 0's disposer"
    );
    assert_eq!(
        SECOND_DISPOSED_VALUE.load(std::sync::atomic::Ordering::SeqCst),
        42,
        "slot 1 uses branch 1's disposer"
    );
    assert_eq!(crate::alloc::dealloc_count() - deallocs_before, 1);
}

/// Helper: allocate a Bind node linking inner IO to a continuation.
/// Layout: [header | tag | inner_io | cont | input_disposer].
fn make_bind_node(inner: i64, cont: i64) -> i64 {
    make_bind_node_with_disposer(inner, cont, ResultDisposer::NONE)
}

fn make_bind_node_with_disposer(inner: i64, cont: i64, input_disposer: ResultDisposer) -> i64 {
    let base = alloc_with_rc(32);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_BIND;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = inner;
        *((base as isize + FIELD_1_OFFSET) as *mut i64) = cont;
        *((base as isize + FIELD_2_OFFSET) as *mut i64) = input_disposer.0;
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

/// A continuation that consumes its transferred argument once and returns
/// `Pure 9`, modelling the compiled ownership of an unused owning parameter.
fn make_consume_and_pure_closure() -> i64 {
    extern "C" fn consume_and_pure(_env_ptr: i64, val: i64) -> i64 {
        count_result_disposal(val);
        make_pure_node_inline(9)
    }
    let base = alloc_with_rc(16);
    unsafe {
        *((base as isize + 16) as *mut i64) = consume_and_pure as *const () as i64;
        *((base as isize + 24) as *mut i64) = 0;
    }
    base as i64
}

// spec: spec/10-io.md §10.12.9 item 4 — Bind's runtime owner transfers the
// produced value before invoking the continuation. The continuation, not both
// layers, performs the one disposal after handoff.
#[test]
fn bind_handoff_disarms_runtime_owner_before_continuation_consumes() {
    RESULT_DISPOSALS.store(0, std::sync::atomic::Ordering::SeqCst);
    let bind = make_bind_node_with_disposer(
        make_pure_node(77),
        make_consume_and_pure_closure(),
        ResultDisposer::from_fn(count_result_disposal),
    );

    assert_eq!(cranelisp_run_io(bind), 9);
    assert_eq!(
        RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
        1,
        "Bind handoff must have exactly one owner, never runtime + continuation"
    );
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

/// Allocate a continuation that returns `node`. When `counted` is true, the
/// return path creates a second counted reference before handing the node to
/// the trampoline; the test retains the allocation's original reference.
fn make_return_node_closure(node: i64, counted: bool) -> i64 {
    extern "C" fn return_unique(env_ptr: i64, _val: i64) -> i64 {
        unsafe { *((env_ptr as isize + 32) as *const i64) }
    }

    extern "C" fn return_counted(env_ptr: i64, _val: i64) -> i64 {
        let node = unsafe { *((env_ptr as isize + 32) as *const i64) };
        crate::rc::rc_inc(node);
        node
    }

    let base = alloc_with_rc(24);
    unsafe {
        *((base as isize + 16) as *mut i64) = if counted {
            return_counted as *const () as i64
        } else {
            return_unique as *const () as i64
        };
        *((base as isize + 24) as *mut i64) = 0;
        *((base as isize + 32) as *mut i64) = node;
    }
    base as i64
}

/// Allocate a Pure node — callable from any context including extern "C".
fn make_pure_node_inline(value: i64) -> i64 {
    let base = alloc_with_rc(24);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_PURE;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = value;
        *((base as isize + FIELD_1_OFFSET) as *mut i64) = 0;
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
/// Layout: [header | tag | count | branch_0 | disposer_0 | ...].
fn make_par_node(branches: &[i64]) -> i64 {
    make_par_node_with_disposers(
        &branches
            .iter()
            .copied()
            .map(|branch| (branch, ResultDisposer::NONE))
            .collect::<Vec<_>>(),
    )
}

fn make_par_node_with_disposers(branches: &[(i64, ResultDisposer)]) -> i64 {
    let payload_size = 8 + 8 + branches.len() * 16;
    let base = alloc_with_rc(payload_size);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_PAR;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = branches.len() as i64;
        for (i, &(branch, disposer)) in branches.iter().enumerate() {
            let offset = FIELD_1_OFFSET + (i as isize) * 16;
            *((base as isize + offset) as *mut i64) = branch;
            *((base as isize + offset + 8) as *mut i64) = disposer.0;
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
        effect_node_on(token, 1, move || {
            order.lock().unwrap().push(id);
            id
        })
    };

    let e0 = make_tracking_effect(1, 0); // token=0, independent
    let e1 = make_tracking_effect(2, 1); // token=1, serial group
    let e2 = make_tracking_effect(3, 1); // token=1, serial group

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
    assert!(
        pos_2 < pos_3,
        "Token=1 effects should run in order: {executed:?}"
    );
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

// spec: spec/12-runtime.md §12.3.1 — a continuation-produced Bind with one
// owner remains reachable through the trampoline walk and tears down exactly
// once. This is the RC1 control for the shared-parent witness below.
#[test]
fn continuation_returned_unique_bind_transfers_and_balances() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();

    let returned_inner = make_pure_node(73);
    let returned_cont = make_identity_pure_closure();
    let returned_bind = make_bind_node(returned_inner, returned_cont);
    let root = make_bind_node(
        make_pure_node(0),
        make_return_node_closure(returned_bind, false),
    );

    assert_eq!(cranelisp_run_io(root), 73);
    assert!(!crate::alloc::is_live(returned_bind as usize));
    assert!(!crate::alloc::is_live(returned_inner as usize));
    assert!(!crate::alloc::is_live(returned_cont as usize));
    assert_eq!(
        crate::alloc::alloc_count() - allocs_before,
        crate::alloc::dealloc_count() - deallocs_before,
        "the unique returned Bind and caller tree must tear down exactly once"
    );
}

// spec: spec/12-runtime.md §12.3.1 — consuming the trampoline's counted
// reference to a continuation-produced Bind must preserve the fields still
// reachable through another live reference to that Bind.
// defect: class=rc-miscount locus=crates/cranelisp-intrinsics/src/io.rs::run_io_trampoline_inner_async found=S122 owner=/dev
#[test]
fn continuation_returned_shared_bind_preserves_retained_parent_fields() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();

    let returned_inner = make_pure_node(73);
    let returned_cont = make_identity_pure_closure();
    let returned_bind = make_bind_node(returned_inner, returned_cont);
    let root = make_bind_node(
        make_pure_node(0),
        make_return_node_closure(returned_bind, true),
    );

    assert_eq!(cranelisp_run_io(root), 73);
    let parent_live = crate::alloc::is_live(returned_bind as usize);
    let inner_live = crate::alloc::is_live(returned_inner as usize);
    let cont_live = crate::alloc::is_live(returned_cont as usize);
    assert!(
        parent_live,
        "the test retains the Bind's original reference"
    );
    assert!(
        inner_live && cont_live,
        "a retained Bind must retain its child references; parent_live={parent_live}, \
         inner_live={inner_live}, cont_live={cont_live}"
    );

    crate::drop::consume_io_tree(crate::handle::test_owned(returned_bind));
    assert_eq!(
        crate::alloc::alloc_count() - allocs_before,
        crate::alloc::dealloc_count() - deallocs_before,
        "releasing the retained parent after the walk must balance the fixture"
    );
}

// ---------------------------------------------------------------------
// The `Pure` payload witness — retain on force
// (`design/intrinsics/ownership-and-disposal.md` §6.1).
// ---------------------------------------------------------------------

/// A `drop<T>` glue with the shape every emitted glue shares for a shallow heap
/// payload: one atomic decrement, with the free strictly inside the
/// last-reference branch.
extern "C" fn drop_shallow_payload(payload: i64) {
    crate::rc::consume_shallow(crate::handle::test_owned(payload));
}

/// Nullary-tag skips taken by [`drop_mixed_payload`]. A `Mixed`-category
/// payload can be a bare tag rather than a pointer, and the emitted glue skips
/// it with the same polarity `rc_inc` does; the counter makes the skip observed
/// rather than assumed.
static MIXED_GLUE_SKIPS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The `Mixed`-category glue shape: the below-threshold skip, then the ordinary
/// shallow release.
extern "C" fn drop_mixed_payload(payload: i64) {
    if payload < cranelisp_types::NULLARY_TAG_THRESHOLD as i64 {
        MIXED_GLUE_SKIPS.fetch_add(1, std::sync::atomic::Ordering::Release);
        return;
    }
    crate::rc::consume_shallow(crate::handle::test_owned(payload));
}

/// Allocate an ABI-10 `Pure` node whose witness is an `Owned(glue)` address —
/// the canonical `drop<T>` entry for the payload's concrete type.
fn make_pure_node_with_glue(payload: i64, glue: extern "C" fn(i64)) -> i64 {
    let base = alloc_with_rc(24);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_PURE;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = payload;
        *((base as isize + FIELD_1_OFFSET) as *mut i64) = glue as *const () as i64;
    }
    base as i64
}

// spec: spec/10-io.md §10.8.1 — T1: an `Owned(glue)` `Pure` released through the
// shallow last-ref path after one force. The consumer discharges the reference
// the force minted; the node still owns its own, and its teardown discharges the
// declared payload field under `SpineTransferred` exactly as under `Structural`.
#[test]
fn forced_pure_node_retains_its_payload_and_shallow_release_discharges_it() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();

    let payload = crate::heap_string::alloc_string(b"t1") as i64;
    let node = make_pure_node_with_glue(payload, drop_shallow_payload);

    let value = force_pure_node(node, false);
    assert_eq!(
        value, payload,
        "the force hands the payload to the consumer"
    );

    // The consumer releases what it was handed, as the edge disposer would.
    drop_shallow_payload(value);
    assert!(
        crate::alloc::is_live(payload as usize),
        "the node keeps its own reference to the payload across a force"
    );
    assert_eq!(crate::alloc::dealloc_count() - deallocs_before, 0);

    crate::drop::dec_shallow_io(crate::handle::test_owned(node));
    assert!(!crate::alloc::is_live(node as usize));
    assert!(
        !crate::alloc::is_live(payload as usize),
        "the node's teardown discharges the payload reference it retained"
    );
    assert_eq!(crate::alloc::alloc_count() - allocs_before, 2);
    assert_eq!(crate::alloc::dealloc_count() - deallocs_before, 2);
}

// spec: spec/10-io.md §10.8.1 — T2: the same node never forced, and forced once
// then released structurally. Both balance, which is the disposition table's
// claim that `Structural` and `SpineTransferred` are one operation for `Pure`.
#[test]
fn unforced_and_forced_pure_nodes_both_balance_under_structural_release() {
    // Leg 1 — never forced (the `Select`-loser / unrun-`Bind` shape): the
    // structural walk discharges the declared payload field.
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();
    let payload = crate::heap_string::alloc_string(b"t2a") as i64;
    let node = make_pure_node_with_glue(payload, drop_shallow_payload);
    crate::drop::consume_io_tree(crate::handle::test_owned(node));
    assert!(!crate::alloc::is_live(payload as usize));
    assert_eq!(crate::alloc::alloc_count() - allocs_before, 2);
    assert_eq!(crate::alloc::dealloc_count() - deallocs_before, 2);

    // Leg 2 — forced once, then released structurally: same outcome.
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();
    let payload = crate::heap_string::alloc_string(b"t2b") as i64;
    let node = make_pure_node_with_glue(payload, drop_shallow_payload);
    drop_shallow_payload(force_pure_node(node, false));
    assert!(
        crate::alloc::is_live(payload as usize),
        "a forced node still owns the payload its structural teardown discharges"
    );
    crate::drop::consume_io_tree(crate::handle::test_owned(node));
    assert!(!crate::alloc::is_live(payload as usize));
    assert_eq!(crate::alloc::alloc_count() - allocs_before, 2);
    assert_eq!(crate::alloc::dealloc_count() - deallocs_before, 2);
}

// spec: spec/10-io.md §10.8.1 — T3: one `Owned(glue)` node with a second owner
// forced twice. Each force yields the live payload and mints one reference for
// its consumer, the node's own reference keeps the payload live past both
// consumer releases, and the last owner's teardown balances the fixture.
#[test]
fn shared_pure_node_forced_twice_yields_its_payload_each_time_and_balances() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();

    let payload = crate::heap_string::alloc_string(b"t3") as i64;
    let node = make_pure_node_with_glue(payload, drop_shallow_payload);
    crate::rc::rc_inc(node); // a second owner — the caller's own tree

    let first = force_pure_node(node, false);
    let second = force_pure_node(node, false);
    assert_eq!(
        (first, second),
        (payload, payload),
        "every forcing of one node is interpreted as the first is"
    );

    drop_shallow_payload(first);
    drop_shallow_payload(second);
    assert!(
        crate::alloc::is_live(payload as usize),
        "each force minted its consumer's reference; the node kept its own"
    );

    crate::drop::dec_shallow_io(crate::handle::test_owned(node));
    assert!(
        crate::alloc::is_live(node as usize) && crate::alloc::is_live(payload as usize),
        "the remaining owner keeps the node and its payload"
    );
    crate::drop::consume_io_tree(crate::handle::test_owned(node));
    assert!(!crate::alloc::is_live(node as usize));
    assert!(!crate::alloc::is_live(payload as usize));
    assert_eq!(crate::alloc::alloc_count() - allocs_before, 2);
    assert_eq!(crate::alloc::dealloc_count() - deallocs_before, 2);
}

// spec: spec/10-io.md §10.8.1 — T3, scalar leg: a `Scalar` witness forced twice
// yields its word each time with no RC operation on either force.
#[test]
fn scalar_pure_node_forced_twice_yields_its_word_with_no_rc_operation() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();

    let node = make_pure_node(42);
    assert_eq!(force_pure_node(node, false), 42);
    assert_eq!(force_pure_node(node, false), 42);
    assert_eq!(
        crate::alloc::dealloc_count() - deallocs_before,
        0,
        "forcing a scalar payload releases nothing"
    );

    crate::drop::dec_shallow_io(crate::handle::test_owned(node));
    assert_eq!(crate::alloc::alloc_count() - allocs_before, 1);
    assert_eq!(crate::alloc::dealloc_count() - deallocs_before, 1);
}

// spec: spec/10-io.md §10.8.1 — T4: an `Owned(glue)` witness over a bare
// nullary-tag payload. `rc_inc` and the emitted glue carry the same
// below-threshold skip, so neither the mint nor either discharge can write at
// `tag + 8`; this cell pins that the skip is the path actually taken on both
// discharges and that the node is the only allocation in play.
#[test]
fn pure_glue_over_a_bare_nullary_tag_payload_touches_no_count() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();
    let skips_before = MIXED_GLUE_SKIPS.load(std::sync::atomic::Ordering::Acquire);

    let tag = 3i64; // a bare nullary-constructor tag, not a heap pointer
    assert!(tag < cranelisp_types::NULLARY_TAG_THRESHOLD as i64);
    let node = make_pure_node_with_glue(tag, drop_mixed_payload);

    assert_eq!(force_pure_node(node, false), tag);
    assert_eq!(force_pure_node(node, false), tag);
    assert_eq!(
        crate::alloc::alloc_count() - allocs_before,
        1,
        "the force allocates nothing"
    );

    // Both consumers release what they were handed, then the node tears down.
    drop_mixed_payload(tag);
    drop_mixed_payload(tag);
    crate::drop::dec_shallow_io(crate::handle::test_owned(node));
    assert_eq!(
        MIXED_GLUE_SKIPS.load(std::sync::atomic::Ordering::Acquire) - skips_before,
        3,
        "the two consumer releases and the node's teardown each ran the glue and \
         took the nullary skip"
    );
    assert_eq!(
        crate::alloc::dealloc_count() - deallocs_before,
        1,
        "only the node was ever an allocation"
    );
}

// ---------------------------------------------------------------------
// The `Effect` thunk — borrowed on force, discharged at teardown
// (`design/intrinsics/ownership-and-disposal.md` §6.2).
// ---------------------------------------------------------------------

/// Counts the forces of a thunk and the destruction of its captures.
#[derive(Clone, Default)]
struct ThunkLedger {
    calls: std::sync::Arc<std::sync::atomic::AtomicUsize>,
    discharges: std::sync::Arc<std::sync::atomic::AtomicUsize>,
}

impl ThunkLedger {
    fn calls(&self) -> usize {
        self.calls.load(std::sync::atomic::Ordering::SeqCst)
    }

    fn discharges(&self) -> usize {
        self.discharges.load(std::sync::atomic::Ordering::SeqCst)
    }
}

/// A capture whose destructor records the thunk's discharge.
struct DischargeSentinel(ThunkLedger);

impl Drop for DischargeSentinel {
    fn drop(&mut self) {
        self.0
            .discharges
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    }
}

/// An `Effect` node whose thunk returns `value` and records each force and its
/// discharge in `ledger`.
fn make_ledgered_effect_node(ledger: &ThunkLedger, value: i64) -> i64 {
    let sentinel = DischargeSentinel(ledger.clone());
    effect_node(move || {
        sentinel
            .0
            .calls
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        value
    })
}

fn force_effect_value(node: i64) -> i64 {
    match force_effect_node(node) {
        EffectStep::Value(value) => value,
        EffectStep::Aborted => panic!("a clean thunk must not fault"),
    }
}

// spec: spec/10-io.md §10.8.1 — E-T1: a node that is never forced (a `Select`
// loser, an unrun `Bind` sub-tree) still owns its thunk; structural teardown
// discharges it once.
#[test]
fn unforced_effect_node_teardown_discharges_its_thunk_once() {
    let ledger = ThunkLedger::default();
    let node = make_ledgered_effect_node(&ledger, 5);

    crate::drop::consume_io_tree(crate::handle::test_owned(node));

    assert!(!crate::alloc::is_live(node as usize));
    assert_eq!((ledger.calls(), ledger.discharges()), (0, 1));
}

// spec: spec/10-io.md §10.8.1 — E-T2: a node with a second owner is forced
// twice. The thunk is borrowed by each force, so both run it and neither
// destroys its captures; the last owner's structural teardown discharges it
// once, after the last call.
#[test]
fn shared_effect_node_forced_twice_keeps_its_thunk_until_last_release() {
    let ledger = ThunkLedger::default();
    let node = make_ledgered_effect_node(&ledger, 21);
    crate::rc::rc_inc(node);

    assert_eq!(force_effect_value(node), 21);
    assert_eq!(force_effect_value(node), 21);
    assert_eq!((ledger.calls(), ledger.discharges()), (2, 0));

    crate::drop::consume_io_tree(crate::handle::test_owned(node));
    assert_eq!(ledger.discharges(), 0, "a remaining owner keeps the thunk");
    crate::drop::consume_io_tree(crate::handle::test_owned(node));
    assert!(!crate::alloc::is_live(node as usize));
    assert_eq!((ledger.calls(), ledger.discharges()), (2, 1));
}

// spec: spec/10-io.md §10.8.1 — E-T3: the trampoline's shallow last-reference
// release after a force discharges the thunk, which is never transferred out
// of the node.
#[test]
fn forced_effect_node_shallow_last_release_discharges_its_thunk_once() {
    let ledger = ThunkLedger::default();
    let node = make_ledgered_effect_node(&ledger, 8);

    assert_eq!(force_effect_value(node), 8);
    crate::drop::dec_shallow_io(crate::handle::test_owned(node));

    assert!(!crate::alloc::is_live(node as usize));
    assert_eq!((ledger.calls(), ledger.discharges()), (1, 1));
}

// spec: spec/10-io.md §10.8.1 — negative leg: a shallow release of one of two
// references is not the node's teardown and discharges nothing.
#[test]
fn releasing_one_of_two_effect_references_discharges_nothing() {
    let ledger = ThunkLedger::default();
    let node = make_ledgered_effect_node(&ledger, 3);
    crate::rc::rc_inc(node);

    crate::drop::dec_shallow_io(crate::handle::test_owned(node));
    assert!(crate::alloc::is_live(node as usize));
    assert_eq!(ledger.discharges(), 0);

    crate::drop::consume_io_tree(crate::handle::test_owned(node));
    assert_eq!(ledger.discharges(), 1);
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
    crate::drop::consume_io_tree(crate::handle::test_owned(result_io));
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
    crate::drop::consume_closure(crate::handle::test_owned(cont_b));
    crate::drop::consume_io_tree(crate::handle::test_owned(result_b));
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
    assert_eq!(
        result, 0,
        "panicking continuation aborts the walk with the sentinel"
    );

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
        drained
            .as_deref()
            .is_some_and(|m| m.contains("division by zero")),
        "the surfaced message must carry the panic cause (got {drained:?})"
    );
    crate::drop::consume_io_tree(crate::handle::test_owned(io));
}

// spec: 10-io §10.12 — read_resource_token returns 0 for non-Effect nodes
#[test]
fn test_read_resource_token() {
    let pure = make_pure_node(42);
    assert_eq!(read_resource_token(pure), 0);

    let effect = effect_node_on(5, 1, || 0);
    assert_eq!(read_resource_token(effect), 5);
    release_io(effect);
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
    let node = make_effect_node(1234);
    let outcome = unsafe {
        crate::io_guard::force_effect_thunk_protected(effect_thunk(node), "stdio/read-line")
    };
    match outcome {
        crate::io_guard::ForceOutcome::Value(v) => assert_eq!(v, 1234),
        crate::io_guard::ForceOutcome::Faulted => panic!("clean thunk must not fault"),
    }
    assert!(
        crate::panic::take_dispatch_fault().is_none(),
        "no dispatch fault on the happy path"
    );
    release_io(node);
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
    let node = faulting_effect_node("device unavailable");
    let outcome = unsafe {
        crate::io_guard::force_effect_thunk_protected(effect_thunk(node), "stdio/read-line")
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
    release_io(node);
}

// spec: design/arch/bounded-contexts.md §4b invariant 14 — a Rust panic in
// foreign platform code is caught DLL-side, returned as a non-null
// fault_cause, and the guard composes a DispatchFault from it.
#[test]
fn force_effect_thunk_protected_dll_caught_panic_is_read() {
    let _ = crate::panic::take_dispatch_fault();
    let _ = crate::panic::take_runtime_error();
    let node = faulting_effect_node("boom in platform fn");
    let outcome =
        unsafe { crate::io_guard::force_effect_thunk_protected(effect_thunk(node), "net/connect") };
    assert!(
        matches!(outcome, crate::io_guard::ForceOutcome::Faulted),
        "DLL-caught panic must surface as a fault"
    );
    let fault = crate::panic::take_dispatch_fault().expect("fault captured");
    assert_eq!(fault.fn_name, "net/connect");
    assert!(fault.cause.contains("boom in platform fn"));
    release_io(node);
}

// spec: design/arch/bounded-contexts.md §5 invariant 9 — the trampoline
// reads the baked fn-name from the Effect node's field-3 (ABI v4) and the
// captured fault carries it. The full-trampoline path exercises the
// field-3 read alongside the force.
#[test]
fn trampoline_effect_fault_reads_baked_fn_name() {
    let _ = crate::panic::take_dispatch_fault();
    let _ = crate::panic::take_runtime_error();
    let node = faulting_effect_node("clock read failed");
    // SAFETY: a fresh, unpublished `Effect` node; field 2 is the fn-name.
    unsafe { crate::heap_access::write_i64(node, FIELD_2_OFFSET, bake_fn_name("clock/now")) };
    let result = run_io_trampoline(node);
    assert_eq!(result, 0, "faulting trampoline returns the sentinel");
    let fault = crate::panic::take_dispatch_fault().expect("fault captured");
    assert_eq!(fault.fn_name, "clock/now", "field-3 fn-name read");
    assert!(fault.cause.contains("clock read failed"));
    release_io(node);
}

// spec: design/arch/bounded-contexts.md §5 invariant 9 — a node the backend
// did NOT stamp (field-3 null) degrades the captured fn-name to
// "<unknown>", never crashing.
#[test]
fn trampoline_effect_fault_null_fn_name_degrades_to_unknown() {
    let _ = crate::panic::take_dispatch_fault();
    let _ = crate::panic::take_runtime_error();
    let node = faulting_effect_node("unstamped fault");
    let result = run_io_trampoline(node);
    assert_eq!(result, 0);
    let fault = crate::panic::take_dispatch_fault().expect("fault captured");
    assert_eq!(
        fault.fn_name, "<unknown>",
        "null field-3 degrades to <unknown>"
    );
    assert!(fault.cause.contains("unstamped fault"));
    release_io(node);
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
    release_io(io);
}

/// Build a BLOCKING `IO_TAG_EFFECT` node carrying the §13.2 widened capacity
/// field (payload tag+thunk+token+fn_name+capacity = 40 bytes), instant thunk.
/// Used by the feature-off negative guard to prove the default build's sync path
/// is unchanged by the capacity append (it ignores capacity — no pool exists).
fn make_capacity_effect_node(token: i64, capacity: i64, value: i64) -> i64 {
    effect_node_on(token, capacity, move || value)
}

fn make_observed_capacity_effect_node(token: i64, capacity: i64, value: i64) -> i64 {
    effect_node_on(token, capacity, move || {
        LATER_SERIAL_EFFECT_RAN.store(true, std::sync::atomic::Ordering::SeqCst);
        value
    })
}

fn make_capacity_runtime_error_effect(token: i64, capacity: i64, message: &'static str) -> i64 {
    effect_node_on(token, capacity, move || {
        crate::panic::set_runtime_error(message.to_string());
        0
    })
}

// spec: design/intrinsics/reactor.md §2.9 — the RETAINED synchronous rayon dispatcher
// (the rayon-worker per-branch driver under the single-trampoline cutover,
// §6.8.0a) token-groups same-token blocking branches via `SerialGroup` and runs
// them WITHOUT any token-capacity `Semaphore` (the appended `capacity` field is
// inert on the sync path — the pool lives only on the async carrier). Negative
// face: the sync `run_par_node` path constructs no pool/parking machinery.
#[test]
fn blocking_par_sync_dispatcher_runs_without_semaphore_neg() {
    // Two same-token (token 5) capacity-2 blocking effects in a Par. On the sync
    // path capacity is inert — the dispatcher token-groups them (SerialGroup) and
    // runs them; the results are marshaled into the Par buffer in binding order.
    let a = make_capacity_effect_node(5, 2, 10);
    let b = make_capacity_effect_node(5, 2, 20);
    let par = make_par_node(&[a, b]);

    // The SYNC dispatcher (`run_par_node`) — the retained rayon-worker driver. No
    // reactor, no pool: `dispatch_par_branches_with_trace` runs the branches.
    let results_buf = run_par_node(par, CancellationProbe::Never, crate::strand::StrandId::ROOT)
        .expect("uncancelled Par completes")
        .transfer();
    let r0 = unsafe { crate::heap_access::read_i64(results_buf, FIELD_0_OFFSET) };
    let r1 = unsafe { crate::heap_access::read_i64(results_buf, FIELD_0_OFFSET + 8) };
    assert_eq!(r0, 10, "blocking branch 0 result via the sync dispatcher");
    assert_eq!(r1, 20, "blocking branch 1 result via the sync dispatcher");

    crate::rc::consume_shallow(crate::handle::test_owned(results_buf));
    crate::drop::consume_io_tree(crate::handle::test_owned(par));
}

// spec: spec/12-runtime.md §12.4.3 + spec/10-io.md §10.12.4 — capacity-1
// same-token effects execute sequentially in source order, and the first error
// aborts the enclosing structured join. A later effect that has not started
// must not be run merely because it shares the already-created Par node.
#[test]
fn serial_group_first_fault_prevents_later_owning_effect() {
    let _ = crate::panic::take_runtime_error();
    RESULT_DISPOSALS.store(0, std::sync::atomic::Ordering::SeqCst);
    LATER_SERIAL_EFFECT_RAN.store(false, std::sync::atomic::Ordering::SeqCst);

    let fault = make_capacity_runtime_error_effect(5, 1, "serial-group fault");
    let owning = make_observed_capacity_effect_node(5, 1, 77);
    let par = make_par_node_with_disposers(&[
        (fault, ResultDisposer::NONE),
        (owning, ResultDisposer::from_fn(count_result_disposal)),
    ]);

    assert!(
        run_par_node(par, CancellationProbe::Never, crate::strand::StrandId::ROOT).is_none(),
        "the branch fault prevents Par from publishing a result buffer"
    );
    assert_eq!(
        crate::panic::take_runtime_error().as_deref(),
        Some("serial-group fault")
    );
    assert_eq!(
        RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
        0,
        "a value that was never produced has no disposal obligation"
    );
    assert!(
        !LATER_SERIAL_EFFECT_RAN.load(std::sync::atomic::Ordering::SeqCst),
        "the first error must abort before the later same-token effect starts"
    );

    crate::drop::consume_io_tree(crate::handle::test_owned(par));
}

// spec: spec/12-runtime.md §12.4.3
// spec: spec/10-io.md §10.12.4.1 item 4
// The async capacity-1 pool preserves the same rule as SerialGroup: a later
// branch that was parked behind the failing source-order predecessor must drop
// its newly acquired permit without spawning its effect.
#[test]
fn async_capacity_one_first_fault_prevents_parked_owning_effect() {
    let _ = crate::panic::take_runtime_error();
    RESULT_DISPOSALS.store(0, std::sync::atomic::Ordering::SeqCst);
    LATER_SERIAL_EFFECT_RAN.store(false, std::sync::atomic::Ordering::SeqCst);

    let fault = make_capacity_runtime_error_effect(6, 1, "async token fault");
    let parked = make_observed_capacity_effect_node(6, 1, 88);
    let par = make_par_node_with_disposers(&[
        (fault, ResultDisposer::NONE),
        (parked, ResultDisposer::from_fn(count_result_disposal)),
    ]);

    let result = crate::reactor::block_on_reactor(async |env| run_par_node_async(par, env).await)
        .expect("reactor completes");
    assert!(result.is_none(), "the first fault aborts the Par result");
    assert_eq!(
        crate::panic::take_runtime_error().as_deref(),
        Some("async token fault")
    );
    assert!(
        !LATER_SERIAL_EFFECT_RAN.load(std::sync::atomic::Ordering::SeqCst),
        "the parked later effect must not be spawned after the first fault"
    );
    assert_eq!(
        RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
        0,
        "an effect that never starts produces no owning result"
    );

    crate::drop::consume_io_tree(crate::handle::test_owned(par));
}

// ===========================================================================
// S94 R1 (FIXME 0457) — the real async Effect arm over `IO_TAG_EFFECT_POLL`.
// Gated `concurrency-runtime` (runs under `cargo nt-concurrency-runtime`).
// ===========================================================================

mod poll_arm {
    use super::*;
    use crate::strand::{StrandEvent, StrandId, drain_strand_events, start_strand_recording};
    use cranelisp_platform::{HostCtx, Poll as CPoll, Waker as CWaker};

    /// A minimal poll-shape leaf: env `[result@0 | arg(N)@8]`. First poll stashes
    /// the absolute deadline in the result slot (a huge value != the `0`
    /// sentinel) and arms a short reactor timer ⇒ `Pending`; on the timer-driven
    /// re-poll it writes `N` to the result slot ⇒ `Ready`. Same shape as the real
    /// `async-demo` leaf, exercising the generic env-offset result read.
    unsafe extern "C" fn test_timer_poll(
        state: *mut core::ffi::c_void,
        host: *const HostCtx,
        waker: *const CWaker,
    ) -> CPoll {
        let result_ptr = state as *mut i64; // env+0 = result slot (also scratch)
        let n = unsafe { *(state as *mut i64).add(1) }; // env+8 = arg N
        let slot = unsafe { *result_ptr };
        if slot == 0 {
            let deadline = crate::reactor::monotonic_nanos() + 2_000_000; // ~2ms
            unsafe { *result_ptr = deadline as i64 };
            let hc = unsafe { &*host };
            unsafe { (hc.register_timer)(hc.host, deadline, waker) };
            CPoll::Pending
        } else if crate::reactor::monotonic_nanos() >= slot as u64 {
            unsafe { *result_ptr = n };
            CPoll::Ready
        } else {
            CPoll::Pending
        }
    }

    /// Build an `IO_TAG_EFFECT_POLL` node over a host-built state-closure whose
    /// `code_ptr` is `test_timer_poll`, `drop_glue` is null, env = `[result=0 |
    /// arg=n]` — exactly the shape the backend's poll-construction arm emits,
    /// INCLUDING the Wave-3 reserved `(token, capacity)` carrier slots at
    /// `field_offset(1)` (abs 32, sentinel 0) and `field_offset(2)` (abs 40,
    /// sentinel 1) — `io-trampoline.md` §13.3.
    fn build_poll_node(n: i64) -> i64 {
        // closure payload: code_ptr(8) + drop_glue(8) + result(8) + arg(8) = 32
        let clo = alloc_with_rc(32) as i64;
        unsafe {
            crate::heap_access::write_i64(clo, 16, test_timer_poll as *const () as i64); // code_ptr
            crate::heap_access::write_i64(clo, 24, 0); // drop_glue null
            crate::heap_access::write_i64(clo, 32, 0); // env: result slot sentinel
            crate::heap_access::write_i64(clo, 40, n); // env: arg 0 = N
        }
        // node payload: tag(8) + state_closure(8) + token(8) + capacity(8) = 32
        // (payload_size(3) — the widened poll node, §13.3).
        let node = alloc_with_rc(32) as i64;
        unsafe {
            crate::heap_access::write_i64(node, TAG_OFFSET, IO_TAG_EFFECT_POLL); // abs 16
            crate::heap_access::write_i64(node, FIELD_0_OFFSET, clo); // abs 24 — state closure
            crate::heap_access::write_i64(node, FIELD_1_OFFSET, 0); // abs 32 — token sentinel
            crate::heap_access::write_i64(node, FIELD_1_OFFSET + 8, 1); // abs 40 — capacity sentinel
        }
        node
    }

    // spec: design/arch/effect-concurrency.md §"The ratified backend↔intrinsics poll-shape Effect-node seam (S94, R1 — the /dev contract)" (b)/(c)
    // — `run_io_trampoline_inner_async` routes an `IO_TAG_EFFECT_POLL` node
    // through an `EffectPoll` await (it suspends on the reactor timer then
    // resumes) and reads the leaf's i64 result generically from the env result
    // slot on `Ready` (no per-effect `ResultReader`). Proves the §4 as-built
    // boundary is closed: the async arm exists + awaits for poll nodes.
    #[test]
    fn run_io_async_effect_arm_awaits_effectpoll_and_reads_generic_result() {
        start_strand_recording();
        let node = build_poll_node(55);
        let result = crate::reactor::block_on_reactor(async |env| {
            run_io_trampoline_inner_async(node, env, StrandId::ROOT, ResultDisposer::NONE).await
        })
        .expect("reactor");
        assert_eq!(
            result,
            TrampolineOutcome::Completed(55),
            "poll node result reads back via the generic env slot"
        );
        let events = drain_strand_events();
        assert!(
            events.contains(&StrandEvent::EffectDispatched {
                strand: StrandId::ROOT
            }),
            "async arm must dispatch an EffectPoll for IO_TAG_EFFECT_POLL: {events:?}"
        );
        assert!(
            events.contains(&StrandEvent::EffectSuspended {
                strand: StrandId::ROOT
            }),
            "poll node must suspend on the reactor: {events:?}"
        );
        assert!(
            events.contains(&StrandEvent::EffectResumed {
                strand: StrandId::ROOT
            }),
            "poll node must resume: {events:?}"
        );
        crate::drop::consume_io_tree(crate::handle::test_owned(node)); // tag-4 consume path frees node + closure
    }

    /// Build an `IO_TAG_EFFECT_POLL` node carrying a LIVE `(token, capacity)` at
    /// the S95-reserved slots (token @ abs 32, capacity @ abs 40) — what the S96
    /// backend poll-construction arm bakes (no longer the sentinel `(0, 1)`).
    fn build_poll_node_tc(n: i64, token: i64, capacity: i64) -> i64 {
        let clo = alloc_with_rc(32) as i64;
        unsafe {
            crate::heap_access::write_i64(clo, 16, test_timer_poll as *const () as i64);
            crate::heap_access::write_i64(clo, 24, 0); // drop_glue null
            crate::heap_access::write_i64(clo, 32, 0); // env: result slot sentinel
            crate::heap_access::write_i64(clo, 40, n); // env: arg 0 = N
        }
        let node = alloc_with_rc(32) as i64;
        unsafe {
            crate::heap_access::write_i64(node, TAG_OFFSET, IO_TAG_EFFECT_POLL); // abs 16
            crate::heap_access::write_i64(node, FIELD_0_OFFSET, clo); // abs 24 — state closure
            crate::heap_access::write_i64(node, FIELD_1_OFFSET, token); // abs 32 — LIVE token
            crate::heap_access::write_i64(node, FIELD_1_OFFSET + 8, capacity); // abs 40 — LIVE capacity
        }
        node
    }

    // spec: design/intrinsics/reactor.md §2.9 §1A — the trampoline reads the LIVE
    // `(token, capacity)` off the `IO_TAG_EFFECT_POLL` node (the S95-reserved
    // slots, now carrying real values), using the SAME offsets the blocking
    // carrier and the backend agree on: token @ abs 32 (`read_resource_token` via
    // FIELD_1_OFFSET), capacity @ abs 40 (`read_capacity` via
    // POLL_CAPACITY_ABS_OFFSET). NOT the sentinel `(0, 1)`. Offset-agreement guard
    // with `io-trampoline.md §13`.
    // design: design/intrinsics/reactor.md §2.9
    #[test]
    fn poll_node_token_capacity_read_live_not_sentinel() {
        // A poll node declaring token 42, capacity 3 reads back the LIVE values.
        let live = build_poll_node_tc(0, 42, 3);
        assert_eq!(
            read_resource_token(live),
            42,
            "poll node token read live off abs offset 32"
        );
        assert_eq!(
            read_capacity(live),
            3,
            "poll node capacity read live off abs offset 40"
        );

        // A sentinel-shaped poll node (token 0, capacity 1) reads back 0/1 — the
        // read distinguishes live from sentinel; it is the SAME read path.
        let sentinel = build_poll_node(7);
        assert_eq!(
            read_resource_token(sentinel),
            0,
            "sentinel poll node token reads 0 (unrestricted)"
        );
        assert_eq!(
            read_capacity(sentinel),
            1,
            "sentinel poll node capacity reads 1"
        );

        crate::drop::consume_io_tree(crate::handle::test_owned(live));
        crate::drop::consume_io_tree(crate::handle::test_owned(sentinel));
    }

    // spec: design/arch/effect-concurrency.md §"The ratified backend↔intrinsics poll-shape Effect-node seam (S94, R1 — the /dev contract)" (b)
    // — the public cfg-on driver `drive_io` (the entry `cranelisp_run_program` /
    // `cranelisp_run_io` route through) forces a poll node through the reactor.
    #[test]
    fn drive_io_routes_poll_node_through_reactor() {
        let node = build_poll_node(42);
        let result = drive_io(node);
        assert_eq!(
            result, 42,
            "drive_io routes a poll node through the reactor"
        );
        crate::drop::consume_io_tree(crate::handle::test_owned(node));
    }

    // spec: design/intrinsics/reactor.md §2.9 §1A — the LIVE poll-carrier acquire wiring:
    // a poll node declaring a non-zero `(token, capacity)` drives through
    // `await_poll_node`, which now READS the live `(token, capacity)`, ACQUIRES the
    // token's permit from `env.pool` before establish, OWNS it on the `EffectPoll`
    // across the suspend/resume arc, and RELEASES it on `Ready` — completing with
    // the generic env-slot result. Proves the acquire-around-poll path is wired on
    // the poll carrier (not just readable), end-to-end through the trampoline.
    // design: design/intrinsics/reactor.md §2.9
    #[test]
    fn live_capacity_poll_node_acquires_owns_releases_through_trampoline() {
        let node = build_poll_node_tc(63, 21, 1); // token 21, capacity 1, result 63
        let result = crate::reactor::block_on_reactor(async |env| {
            // The pool starts empty; the poll path creates + acquires token 21's
            // slot, holds it across the arc, and releases on Ready.
            run_io_trampoline_inner_async(node, env, StrandId::ROOT, ResultDisposer::NONE).await
        })
        .expect("reactor");
        assert_eq!(
            result,
            TrampolineOutcome::Completed(63),
            "live-capacity poll node completes (acquire→own→release) via the generic env slot"
        );
        crate::drop::consume_io_tree(crate::handle::test_owned(node));
    }

    /// A poll fixture with a CALLER-CHOSEN timer delay (vs `test_timer_poll`'s
    /// fixed ~2ms). env = `[result/scratch@0 | delay_ms@8 | retval@16]`: first
    /// poll arms a `delay_ms` reactor timer ⇒ `Pending`; the timer-driven re-poll
    /// writes `retval` ⇒ `Ready`. Used to make the poll branch take a meaningful,
    /// overlap-observable time.
    unsafe extern "C" fn slow_timer_poll(
        state: *mut core::ffi::c_void,
        host: *const HostCtx,
        waker: *const CWaker,
    ) -> CPoll {
        let result_ptr = state as *mut i64;
        let delay_ms = unsafe { *(state as *mut i64).add(1) };
        let retval = unsafe { *(state as *mut i64).add(2) };
        let slot = unsafe { *result_ptr };
        if slot == 0 {
            let deadline = crate::reactor::monotonic_nanos() + (delay_ms as u64) * 1_000_000;
            unsafe { *result_ptr = deadline as i64 };
            let hc = unsafe { &*host };
            unsafe { (hc.register_timer)(hc.host, deadline, waker) };
            CPoll::Pending
        } else if crate::reactor::monotonic_nanos() >= slot as u64 {
            unsafe { *result_ptr = retval };
            CPoll::Ready
        } else {
            CPoll::Pending
        }
    }

    /// Build a poll node over `slow_timer_poll` with a `delay_ms` timer returning
    /// `retval`. Widened poll node (reserved `(token, capacity)` sentinels, §13.3).
    fn build_slow_poll_node(delay_ms: i64, retval: i64) -> i64 {
        // closure payload: code_ptr(8)+drop_glue(8)+result(8)+delay(8)+retval(8)=40
        let clo = alloc_with_rc(40) as i64;
        unsafe {
            crate::heap_access::write_i64(clo, 16, slow_timer_poll as *const () as i64);
            crate::heap_access::write_i64(clo, 24, 0); // drop_glue null
            crate::heap_access::write_i64(clo, 32, 0); // env: result slot sentinel
            crate::heap_access::write_i64(clo, 40, delay_ms); // env: delay
            crate::heap_access::write_i64(clo, 48, retval); // env: retval
        }
        let node = alloc_with_rc(32) as i64; // payload_size(3) widened poll node
        unsafe {
            crate::heap_access::write_i64(node, TAG_OFFSET, IO_TAG_EFFECT_POLL);
            crate::heap_access::write_i64(node, FIELD_0_OFFSET, clo);
            crate::heap_access::write_i64(node, FIELD_1_OFFSET, 0); // token sentinel
            crate::heap_access::write_i64(node, FIELD_1_OFFSET + 8, 1); // capacity sentinel
        }
        node
    }

    /// Build a BLOCKING `IO_TAG_EFFECT` node (widened with the §13.2 capacity
    /// field) whose thunk SLEEPS `sleep_ms` then returns `value`. Models the
    /// `pool-demo` blocking leaf at the unit tier.
    fn build_sleeping_blocking_effect(token: i64, capacity: i64, sleep_ms: u64, value: i64) -> i64 {
        effect_node_on(token, capacity, move || {
            BLOCKING_EFFECT_ENTERED.store(true, std::sync::atomic::Ordering::Release);
            std::thread::sleep(std::time::Duration::from_millis(sleep_ms));
            value
        })
    }

    /// Build a blocking leaf whose worker cannot publish until the test has
    /// observed the branch future suspended on its receiver.
    fn build_gated_blocking_effect(start: std::sync::Arc<std::sync::Barrier>, value: i64) -> i64 {
        effect_node_on(0, 1, move || {
            start.wait();
            value
        })
    }

    // spec: spec/10-io.md §10.12.9 — a blocking Select loser whose owning
    // result was successfully published into the bridge is disposed exactly
    // once when cancellation drops the ready receiver before its next poll.
    #[test]
    fn ready_blocking_loser_disposes_successfully_published_result_once() {
        const VALUE: i64 = 83;
        RESULT_DISPOSALS.store(0, std::sync::atomic::Ordering::SeqCst);
        FIRST_DISPOSED_VALUE.store(0, std::sync::atomic::Ordering::SeqCst);
        let start = std::sync::Arc::new(std::sync::Barrier::new(2));
        let node = build_gated_blocking_effect(start.clone(), VALUE);
        let handoff = install_ready_handoff_test_barrier(node);

        crate::reactor::block_on_reactor(async |env| {
            let branch = ParBranch {
                io: node,
                disposer: ResultDisposer::from_fn(record_first_disposal),
            };
            let mut running = Box::pin(run_blocking_branch(0, branch, env));
            let waker = futures::task::noop_waker();
            let mut context = std::task::Context::from_waker(&waker);
            assert!(matches!(
                std::future::Future::poll(running.as_mut(), &mut context),
                std::task::Poll::Pending
            ));
            start.wait();
            handoff.wait_until_published();

            drop(running);
            assert_eq!(
                RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
                1,
                "dropping the ready receiver must dispose its queued owner once"
            );
            assert_eq!(
                FIRST_DISPOSED_VALUE.load(std::sync::atomic::Ordering::SeqCst),
                VALUE,
                "the queued payload's exact value reaches its disposer"
            );
            handoff.release_and_wait_until_finished();
            0
        })
        .expect("reactor");
        crate::drop::consume_io_tree(crate::handle::test_owned(node));
    }

    // spec: spec/10-io.md §10.12.9 — polling the same ready handoff transfers
    // its result outward; only the receiving caller performs the one disposal.
    #[test]
    fn ready_blocking_winner_transfers_result_to_caller() {
        const VALUE: i64 = 89;
        RESULT_DISPOSALS.store(0, std::sync::atomic::Ordering::SeqCst);
        FIRST_DISPOSED_VALUE.store(0, std::sync::atomic::Ordering::SeqCst);
        let start = std::sync::Arc::new(std::sync::Barrier::new(2));
        let node = build_gated_blocking_effect(start.clone(), VALUE);
        let handoff = install_ready_handoff_test_barrier(node);

        crate::reactor::block_on_reactor(async |env| {
            let disposer = ResultDisposer::from_fn(record_first_disposal);
            let branch = ParBranch { io: node, disposer };
            let mut running = Box::pin(run_blocking_branch(0, branch, env));
            let waker = futures::task::noop_waker();
            let mut context = std::task::Context::from_waker(&waker);
            assert!(matches!(
                std::future::Future::poll(running.as_mut(), &mut context),
                std::task::Poll::Pending
            ));
            start.wait();
            handoff.wait_until_published();

            let (_, produced) = match std::future::Future::poll(running.as_mut(), &mut context) {
                std::task::Poll::Ready(output) => output,
                std::task::Poll::Pending => panic!("published receiver must now be ready"),
            };
            let produced = produced.expect("the ready branch publishes its owning value");
            assert_eq!(
                RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
                0,
                "receiving the ready value must transfer rather than dispose it"
            );
            let value = produced.transfer();
            assert_eq!(value, VALUE);
            disposer.dispose(value);
            assert_eq!(
                RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
                1,
                "the receiving caller releases the transferred value exactly once"
            );
            assert_eq!(
                FIRST_DISPOSED_VALUE.load(std::sync::atomic::Ordering::SeqCst),
                VALUE
            );
            handoff.release_and_wait_until_finished();
            0
        })
        .expect("reactor");
        crate::drop::consume_io_tree(crate::handle::test_owned(node));
    }

    // spec: spec/10-io.md §10.12.9 item 4 — cancelling an admitted blocking
    // branch does not interrupt the foreign call; when it returns later, the
    // worker disposes the result instead of suppressing an owned value.
    #[test]
    fn cancelled_blocking_branch_disposes_its_late_result_worker_side() {
        RESULT_DISPOSALS.store(0, std::sync::atomic::Ordering::SeqCst);
        BLOCKING_EFFECT_ENTERED.store(false, std::sync::atomic::Ordering::Release);
        let node = build_sleeping_blocking_effect(0, 1, 20, 77);
        crate::reactor::block_on_reactor(async |env| {
            let branch = ParBranch {
                io: node,
                disposer: ResultDisposer::from_fn(count_result_disposal),
            };
            let mut running = Box::pin(run_blocking_branch(0, branch, env));
            let waker = futures::task::noop_waker();
            let mut context = std::task::Context::from_waker(&waker);
            assert!(
                matches!(
                    std::future::Future::poll(running.as_mut(), &mut context),
                    std::task::Poll::Pending
                ),
                "the first poll admits and spawns the delayed worker"
            );
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(1);
            while !BLOCKING_EFFECT_ENTERED.load(std::sync::atomic::Ordering::Acquire)
                && std::time::Instant::now() < deadline
            {
                std::thread::yield_now();
            }
            assert!(
                BLOCKING_EFFECT_ENTERED.load(std::sync::atomic::Ordering::Acquire),
                "the foreign call must be entered before cancellation"
            );
            drop(running);
            0
        })
        .expect("reactor");
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(1);
        while RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst) == 0
            && std::time::Instant::now() < deadline
        {
            std::thread::yield_now();
        }
        assert_eq!(
            RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
            1,
            "the cancelled worker's late result is disposed exactly once"
        );
        crate::drop::consume_io_tree(crate::handle::test_owned(node));
    }

    // spec: design/intrinsics/reactor.md §2.6 (two-pool join) — a mixed `Par` of one
    // BLOCKING branch (→ rayon, across the wakeable bridge) and one POLL branch
    // (→ reactor) overlaps on BOTH pools: the blocking branch offloaded to rayon
    // does NOT starve the reactor, so the poll branch progresses concurrently and
    // the join completes in ≈max(delay) not sum. The load-bearing Principle-8
    // guard against the slice-6 starvation regression.
    #[test]
    fn two_pool_join_blocking_branch_does_not_starve_reactor() {
        const DELAY_MS: u64 = 50;
        // Branch 0: blocking, sleeps 50ms on rayon, token 0 (no acquire), → 7.
        let blocking = build_sleeping_blocking_effect(0, 1, DELAY_MS, 7);
        // Branch 1: poll, 50ms reactor timer, → 9.
        let poll = build_slow_poll_node(DELAY_MS as i64, 9);
        let par = make_par_node(&[blocking, poll]);

        let start = std::time::Instant::now();
        let results_buf = crate::reactor::block_on_reactor(async |env| {
            run_par_node_async(par, env)
                .await
                .expect("uncancelled Par completes")
                .transfer()
        })
        .expect("reactor");
        let elapsed_ms = start.elapsed().as_millis() as u64;

        // Both branches ran; results merged in binding order.
        let r0 = unsafe { crate::heap_access::read_i64(results_buf, FIELD_0_OFFSET) };
        let r1 = unsafe { crate::heap_access::read_i64(results_buf, FIELD_0_OFFSET + 8) };
        assert_eq!(r0, 7, "blocking branch (idx 0) result");
        assert_eq!(r1, 9, "poll branch (idx 1) result");

        // OVERLAP: ≈max(50ms) not sum(100ms). If the blocking branch starved the
        // reactor (ran ON the reactor thread / block_on'd the rayon join), the
        // poll's 50ms timer would only start AFTER the 50ms sleep ⇒ ≈100ms.
        assert!(
            elapsed_ms < DELAY_MS * 3 / 2,
            "mixed blocking+poll Par must OVERLAP on both pools (≈{DELAY_MS}ms, \
             not sum {}ms); measured {elapsed_ms}ms — the blocking branch is \
             starving the reactor",
            DELAY_MS * 2,
        );

        // Cleanup: free the merged results buffer + the Par tree.
        crate::rc::consume_shallow(crate::handle::test_owned(results_buf));
        crate::drop::consume_io_tree(crate::handle::test_owned(par));
    }

    /// A continuation closure `(fn [_] <captured-node>)` — ignores its argument
    /// and returns a pre-built IO node pointer (captured at env+32). Models the
    /// launch loop's `(fn [_r] (recur …))` tail, where the continuation produces
    /// the next IO tree rather than a `Pure`. `drop_glue` null (the captured node
    /// is owned by the trampoline that consumes it, not the closure).
    fn make_return_node_closure(node: i64) -> i64 {
        extern "C" fn ret_node(env_ptr: i64, _val: i64) -> i64 {
            unsafe { *((env_ptr as isize + 32) as *const i64) }
        }
        let base = alloc_with_rc(24); // code_ptr + drop_glue + 1 capture
        unsafe {
            *((base as isize + 16) as *mut i64) = ret_node as *const () as i64;
            *((base as isize + 24) as *mut i64) = 0; // drop_glue null
            *((base as isize + 32) as *mut i64) = node; // captured next-node
        }
        base as i64
    }

    // spec: spec/10-io.md §10.12.4.2 item 3 / design/intrinsics/reactor.md §2.13 — a launch
    // LOOP under a global degree D bounds in-flight DETACHED strands to D: the
    // (D+1)th launch PARKS on `acquire_global`, then RESUMES when an in-flight
    // strand completes and frees a global slot. The regression this guards: when
    // the launcher parks on `acquire_global` and the last in-flight strand
    // completes DURING `supervisor.drive()` (freeing the budget + waking the parked
    // launch), the executor loop reached the `would hang` panic guard — no fd/timer
    // waiter, supervisor empty, top not done — and FALSELY aborted, even though the
    // launcher was just woken and only needed a re-poll. The `woken` pending-wake
    // flag suppresses that false hang. Without the fix this `block_on_reactor`
    // drive panics; with it the launch loop drains cleanly and the launcher reaches
    // its `(Pure 42)`.
    // design: design/intrinsics/reactor.md §2.13
    #[test]
    fn degree_parked_launcher_resumes_when_strand_frees_budget_no_false_hang() {
        // SAFETY: nextest runs each test in its own process, so this env mutation
        // is isolated (no other test observes it). degree 1 ⇒ global budget 1.
        unsafe { std::env::set_var("CRANELISP_DEGREE", "1") };
        start_strand_recording();

        // Bind(Launch(poll1), (fn [_] Bind(Launch(poll2), (fn [_] Pure 42)))):
        // a 2-iteration launch loop. Under degree 1 the launch of poll2 PARKS on
        // the global budget held by poll1; poll1's reactor timer fires, the strand
        // completes + frees the budget, and the parked launch resumes.
        let pure42 = make_pure_node(42);
        let launch2 = make_launch_node(build_poll_node(2));
        let bind_inner = make_bind_node(launch2, make_return_node_closure(pure42));
        let launch1 = make_launch_node(build_poll_node(1));
        let bind_outer = make_bind_node(launch1, make_return_node_closure(bind_inner));

        let result = cranelisp_run_io(bind_outer);
        unsafe { std::env::remove_var("CRANELISP_DEGREE") };

        assert_eq!(
            result, 42,
            "the degree-parked launcher must RESUME when an in-flight strand frees \
             the global budget — the loop drains to (Pure 42), NOT a false `would \
             hang` abort"
        );
        let events = drain_strand_events();
        // Both detached strands ran to completion (drained before exit, §2.12).
        let completed = events
            .iter()
            .filter(|e| matches!(e, StrandEvent::StrandCompleted { .. }))
            .count();
        assert_eq!(
            completed, 2,
            "both launched strands drained before exit: {events:?}"
        );
        // The (D+1)th launch PARKED on the global budget, then resumed (the
        // backpressure witness at the unit tier).
        assert!(
            events.contains(&StrandEvent::GlobalBudgetParked {
                strand: StrandId(2)
            }) || events
                .iter()
                .any(|e| matches!(e, StrandEvent::GlobalBudgetParked { .. })),
            "the over-budget launch parked on the global budget: {events:?}"
        );
    }

    /// An always-`Pending` poll-fn that arms NO reactor interest — models a leaf
    /// parked-on-readiness that never completes (the cancelled-branch subject). Used
    /// to suspend a branch future mid-flight so the §2.15.1 drop-guard can be
    /// observed.
    unsafe extern "C" fn never_ready_pollfn(
        _state: *mut core::ffi::c_void,
        _host: *const HostCtx,
        _waker: *const CWaker,
    ) -> CPoll {
        CPoll::Pending
    }

    /// Build an `IO_TAG_EFFECT_POLL` node over `never_ready_pollfn`, token 0 (no
    /// admission). Two `alloc_with_rc` chunks: the state closure + the node.
    fn build_never_ready_poll_node() -> i64 {
        let clo = alloc_with_rc(32) as i64;
        unsafe {
            crate::heap_access::write_i64(clo, 16, never_ready_pollfn as *const () as i64);
            crate::heap_access::write_i64(clo, 24, 0); // drop_glue null
            crate::heap_access::write_i64(clo, 32, 0); // env: result slot
            crate::heap_access::write_i64(clo, 40, 0); // env: pad/arg
        }
        let node = alloc_with_rc(32) as i64;
        unsafe {
            crate::heap_access::write_i64(node, TAG_OFFSET, IO_TAG_EFFECT_POLL);
            crate::heap_access::write_i64(node, FIELD_0_OFFSET, clo);
            crate::heap_access::write_i64(node, FIELD_1_OFFSET, 0); // token 0 (no acquire)
            crate::heap_access::write_i64(node, FIELD_1_OFFSET + 8, 1); // capacity 1
        }
        node
    }

    /// Poll a boxed trampoline future once with a noop waker.
    fn poll_boxed(
        f: &mut std::pin::Pin<Box<dyn std::future::Future<Output = TrampolineOutcome> + '_>>,
    ) -> std::task::Poll<TrampolineOutcome> {
        let w = futures::task::noop_waker();
        let mut cx = std::task::Context::from_waker(&w);
        f.as_mut().poll(&mut cx)
    }

    // spec: design/intrinsics/reactor.md §2.15.1 — the trampoline-frame cancellation
    // drop-guard. A branch future suspended on a FRESH (continuation-produced)
    // in-flight poll node, then DROPPED mid-flight (a cancelled race/select loser),
    // must FREE that fresh subtree (node + state closure) via the `TrampolineFrame`
    // drop-guard. Without the guard the fresh in-flight node leaks (it has no other
    // owner — its producing Bind was already dec'd). `Bind(Pure 0, (fn [_] <fresh
    // poll node>))` steps Pure→continuation→the poll node (now fresh) → suspends;
    // dropping the future there frees the fresh node.
    // design: design/intrinsics/reactor.md §2.15.1
    #[test]
    fn cancelled_branch_future_frees_fresh_inflight_subtree() {
        // The poll node becomes a FRESH in-flight node when the continuation returns
        // it (Step::Advance ⇒ current_is_fresh = true).
        let poll = build_never_ready_poll_node(); // 2 allocs: node + closure
        let cont = make_return_node_closure(poll); // (fn [_] <captured poll node>)
        let inner = make_pure_node(0);
        let bind = make_bind_node(inner, cont);

        let d_before = crate::alloc::dealloc_count();
        crate::reactor::block_on_reactor(async |env| {
            let mut fut =
                run_io_trampoline_inner_async(bind, env, StrandId::ROOT, ResultDisposer::NONE);
            // One poll drives Pure → continuation → the fresh poll node → Pending.
            assert!(
                matches!(poll_boxed(&mut fut), std::task::Poll::Pending),
                "the branch suspends on the fresh in-flight poll node"
            );
            drop(fut); // CANCEL mid-flight → the frame guard frees the fresh subtree.
            0
        })
        .expect("reactor");
        let freed = crate::alloc::dealloc_count() - d_before;
        assert!(
            freed >= 2,
            "the cancelled branch must free its FRESH in-flight poll node + state closure \
             via the §2.15.1 drop-guard (freed {freed}; a leak frees 0)"
        );

        // The caller's tree (Bind + Pure + cont closure) is non-fresh — the guard
        // leaves it to its owner; release it so the test is leak-clean. (The fresh
        // poll node was already consumed by the guard, so it is NOT in this walk.)
        crate::drop::consume_io_tree(crate::handle::test_owned(bind));
    }
}

// ===========================================================================
// S96 Chunk B §2.11/§2.12 — the `IO_TAG_LAUNCH` launch-and-continue arm +
// the supervisor (catch + StrandFailed + drive survives). These drive a real
// `Bind(Launch(sub), cont)` tree through `cranelisp_run_io` (the ASYNC
// trampoline — the launch arm exists only there; the sync stepper never sees an
// `IO_TAG_LAUNCH` node), so the launch detaches the sub-tree into the supervisor
// and the continuation proceeds without awaiting it.
// design: design/intrinsics/reactor.md §2.11 / §2.12
// ===========================================================================

use crate::strand::{StrandEvent, StrandId, drain_strand_events, start_strand_recording};

/// Build a thin `IO_TAG_LAUNCH` node wrapping `sub_tree` at field 0 (the backend's
/// `compile_launch` shape, `io-trampoline.md §15.4`).
fn make_launch_node(sub_tree: i64) -> i64 {
    make_launch_node_with_disposer(sub_tree, ResultDisposer::NONE)
}

fn make_launch_node_with_disposer(sub_tree: i64, result_disposer: ResultDisposer) -> i64 {
    let base = alloc_with_rc(24);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_LAUNCH;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = sub_tree;
        *((base as isize + FIELD_1_OFFSET) as *mut i64) = result_disposer.0;
    }
    base as i64
}

/// Build an IO node with an arbitrary (here: bogus) tag — the async trampoline
/// `panic!`s on an unknown tag, modelling a strand that faults mid-flight.
fn make_bogus_tag_node(tag: i64) -> i64 {
    let base = alloc_with_rc(16); // tag + field0 (consume_io_tree snapshots field0)
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = tag;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = 0;
    }
    base as i64
}

/// Build an `IO_TAG_EFFECT` node whose thunk raises a RUNTIME ERROR (sets the
/// thread-local error slot, as `runtime_panic` does) then returns `0` — so the
/// strand's completion-boundary `take_runtime_error` capture (§2.12) sees it.
fn make_runtime_error_effect(msg: &'static str) -> i64 {
    effect_node(move || {
        crate::panic::set_runtime_error(msg.to_string());
        0
    })
}

// spec: spec/10-io.md §10.12.7 — launch-and-continue: a launched effect runs
// DETACHED while the launcher continues WITHOUT awaiting it. `Bind(Launch(Pure
// 999), (fn [x] (Pure (+ x 77))))`: the launch yields `Pure Unit` (0), so the
// continuation runs with 0 ⇒ 77 — NOT the launched 999 (the launcher did not
// await). The detached strand still RAN (drained before exit: StrandLaunched +
// StrandCompleted), under the root strand.
// design: design/intrinsics/reactor.md §2.11
#[test]
fn launch_arm_detaches_subtree_continuation_proceeds_without_awaiting() {
    start_strand_recording();
    let sub = make_pure_node(999); // the launched (discarded-result) sub-tree
    let launch = make_launch_node(sub);
    let cont = make_add_and_pure_closure(77); // (fn [x] (Pure (+ x 77)))
    let bind = make_bind_node(launch, cont);

    let result = cranelisp_run_io(bind);
    assert_eq!(
        result, 77,
        "the continuation proceeds on the launch's Pure Unit (0+77), NOT the \
         launched 999 — the launcher did not await the detached effect"
    );

    let events = drain_strand_events();
    assert!(
        events.iter().any(
            |e| matches!(e, StrandEvent::StrandLaunched { parent, .. } if *parent == StrandId::ROOT)
        ),
        "the launch records StrandLaunched under the root strand: {events:?}"
    );
    assert!(
        events
            .iter()
            .any(|e| matches!(e, StrandEvent::StrandCompleted { .. })),
        "the detached strand RAN to completion (drained before exit): {events:?}"
    );
}

// spec: spec/10-io.md §10.12.9 item 4 — no language caller observes a
// detached Launch result, so the supervisor consumes its carried result exactly
// once after successful completion.
#[test]
fn launch_supervisor_disposes_unobserved_owning_result_once() {
    RESULT_DISPOSALS.store(0, std::sync::atomic::Ordering::SeqCst);
    let launch = make_launch_node_with_disposer(
        make_pure_node(999),
        ResultDisposer::from_fn(count_result_disposal),
    );
    let bind = make_bind_node(launch, make_add_and_pure_closure(77));

    assert_eq!(cranelisp_run_io(bind), 77);
    assert_eq!(
        RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
        1,
        "the drained supervisor owns and disposes the detached result exactly once"
    );
}

// spec: spec/12-runtime.md §12.7.9 — a launched (detached) strand that PANICS is
// contained by the supervisor: caught (`catch_unwind`), recorded (`StrandFailed`,
// not silently dropped), the drive SURVIVES (the launcher's continuation still
// completes), and the panic is NEVER re-raised (the runtime-error slot stays
// clear). A non-supervised detached panic would abort the whole drive.
// design: design/intrinsics/reactor.md §2.12
#[test]
fn supervisor_catches_panicking_strand_records_failed_drive_survives() {
    // Silence the EXPECTED panic's default hook output (nextest isolates this
    // process, so the global hook swap is safe).
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    start_strand_recording();

    let bogus = make_bogus_tag_node(999); // the async trampoline panics on it
    let launch = make_launch_node(bogus);
    let cont = make_add_and_pure_closure(5); // (fn [x] (Pure (+ x 5)))
    let bind = make_bind_node(launch, cont);

    let result = cranelisp_run_io(bind);
    std::panic::set_hook(prev);

    assert_eq!(
        result, 5,
        "the drive SURVIVED the strand panic — the launcher's continuation \
         completed (0+5), the server lives"
    );
    // Never re-raised: a caught panic is NOT ferried into the runtime-error slot.
    assert!(
        crate::panic::take_runtime_error().is_none(),
        "the supervisor must catch + drop, never re-raise the panic into the slot"
    );

    let events = drain_strand_events();
    assert!(
        events.iter().any(
            |e| matches!(e, StrandEvent::StrandFailed { message, .. } if message == "<panicked>")
        ),
        "a panicking strand must record StrandFailed (NOT a silent drop): {events:?}"
    );
}

// spec: spec/12-runtime.md §12.7.9 — the supervisor catches the OTHER failure
// kind too: a strand whose effect raises a RUNTIME ERROR is captured at the
// completion boundary (`take_runtime_error`, reused from the S95 ferry) →
// StrandFailed{message} with the ferried message, the drive survives, and the
// error is captured (taken), not re-raised into the host slot.
// design: design/intrinsics/reactor.md §2.12
#[test]
fn supervisor_catches_runtime_error_strand_records_failed_with_message() {
    start_strand_recording();
    let sub = make_runtime_error_effect("eff-boom"); // raises a runtime error mid-strand
    let launch = make_launch_node(sub);
    let cont = make_add_and_pure_closure(3);
    let bind = make_bind_node(launch, cont);

    let result = cranelisp_run_io(bind);
    assert_eq!(
        result, 3,
        "the launcher's continuation completed (0+3); the drive survived"
    );

    let events = drain_strand_events();
    assert!(
        events.iter().any(
            |e| matches!(e, StrandEvent::StrandFailed { message, .. } if message == "eff-boom")
        ),
        "a runtime-error strand records StrandFailed with the ferried message: {events:?}"
    );
    // The supervisor TOOK the error at the strand's completion boundary (captured,
    // not left in the slot to re-raise into the host).
    assert!(
        crate::panic::take_runtime_error().is_none(),
        "the runtime error was captured by the strand, not re-raised"
    );
}

/// Build a degenerate empty `IO_TAG_SELECT` node — `[header | tag=6 | branch_vec]`
/// with a NULL branch-vec pointer (field 0 = 0), which `read_select_branches`
/// reads back as zero branches (the `(select [])` shape).
fn make_empty_select_node() -> i64 {
    let base = alloc_with_rc(24);
    unsafe {
        *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_SELECT;
        *((base as isize + FIELD_0_OFFSET) as *mut i64) = 0; // null vec ⇒ empty
        *((base as isize + FIELD_1_OFFSET) as *mut i64) = 0; // result disposer
    }
    base as i64
}

fn make_select_node(branches: &[i64], result_disposer: ResultDisposer) -> i64 {
    let branch_vec = alloc_with_rc(24) as i64;
    let data = crate::vec_runtime::alloc_data_buffer(branches.len() as i64);
    unsafe {
        crate::heap_access::write_i64(
            branch_vec,
            crate::vec_runtime::LEN_OFFSET as isize,
            branches.len() as i64,
        );
        crate::heap_access::write_i64(
            branch_vec,
            crate::vec_runtime::CAP_OFFSET as isize,
            branches.len() as i64,
        );
        crate::heap_access::write_i64(
            branch_vec,
            crate::vec_runtime::DATA_PTR_OFFSET as isize,
            data as i64,
        );
        for (index, branch) in branches.iter().copied().enumerate() {
            crate::heap_access::write_i64(data as i64, (index as isize) * 8, branch);
        }
    }

    let node = alloc_with_rc(24) as i64;
    unsafe {
        crate::heap_access::write_i64(node, TAG_OFFSET, IO_TAG_SELECT);
        crate::heap_access::write_i64(node, FIELD_0_OFFSET, branch_vec);
        crate::heap_access::write_i64(node, FIELD_1_OFFSET, result_disposer.0);
    }
    node
}

// spec: spec/10-io.md §10.12.9 item 4 — Select's common disposer guards
// branch results only until a winner transfers outward. The top-level caller,
// not the runtime race, owns the returned winner.
#[test]
fn select_winner_transfers_common_disposer_to_top_level_caller() {
    RESULT_DISPOSALS.store(0, std::sync::atomic::Ordering::SeqCst);
    let disposer = ResultDisposer::from_fn(count_result_disposal);
    let select = make_select_node(&[make_pure_node(11), make_pure_node(22)], disposer);

    let winner = cranelisp_run_io(select);
    assert!(winner == 11 || winner == 22);
    assert_eq!(
        RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
        0,
        "Select must disarm the winning branch before returning it"
    );
    disposer.dispose(winner);
    assert_eq!(
        RESULT_DISPOSALS.load(std::sync::atomic::Ordering::SeqCst),
        1,
        "the top-level receiver owns the transferred winner exactly once"
    );
}

// A witness the empty-select continuation was invoked (it MUST NOT be — the
// sentinel `0` an empty select produces is never applied to the continuation).
static EMPTY_SELECT_CONT_RAN: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// A continuation `(fn [_] (Pure 99))` that RECORDS it was invoked. Used to prove
/// the empty-select abort fires BEFORE the continuation runs (FIXME 0475).
fn make_flag_setting_cont() -> i64 {
    extern "C" fn flag_cont(_env_ptr: i64, _val: i64) -> i64 {
        EMPTY_SELECT_CONT_RAN.store(true, std::sync::atomic::Ordering::SeqCst);
        make_pure_node_inline(99)
    }
    let base = alloc_with_rc(16); // code_ptr + drop_glue_ptr = 16
    unsafe {
        *((base as isize + 16) as *mut i64) = flag_cont as *const () as i64;
        *((base as isize + 24) as *mut i64) = 0;
    }
    base as i64
}

// spec: design/intrinsics/reactor.md §9 / spec/10-io.md §10.12.8 — a degenerate empty
// `(select [])` MUST raise a recoverable runtime error ("select over empty
// collection") through the standard runtime-error slot, NOT return a synthesised
// Unit `0` and NOT hang. The trampoline aborts BEFORE feeding the sentinel to the
// bind continuation (at a heap-typed `a` the `0` is an unsound null the
// continuation would dereference), so the continuation MUST NOT run. FIXME 0475.
#[test]
fn empty_select_raises_runtime_error_and_does_not_feed_continuation() {
    // Clear any stale slot + flag so we observe only this run.
    let _ = crate::panic::take_runtime_error();
    EMPTY_SELECT_CONT_RAN.store(false, std::sync::atomic::Ordering::SeqCst);

    let select = make_empty_select_node();
    let cont = make_flag_setting_cont();
    let bind = make_bind_node(select, cont);

    let result = crate::reactor::block_on_reactor(async |env| {
        run_io_trampoline_inner_async(bind, env, StrandId::ROOT, ResultDisposer::NONE).await
    })
    .expect("reactor");

    // The sentinel is returned (the trampoline aborts to `0`; int reads the slot,
    // not the return value).
    assert_eq!(
        result,
        TrampolineOutcome::Stopped,
        "an aborted empty-select drive produces no value"
    );
    // The runtime-error slot carries the message of record.
    assert_eq!(
        crate::panic::take_runtime_error().as_deref(),
        Some("select over empty collection"),
        "empty (select []) must raise the runtime error 'select over empty collection' \
         via the standard slot (reactor.md §9 / spec/10-io.md §10.12.8)"
    );
    // The bind continuation MUST NOT have run — the sentinel `0` was never applied.
    assert!(
        !EMPTY_SELECT_CONT_RAN.load(std::sync::atomic::Ordering::SeqCst),
        "the empty-select sentinel 0 MUST NOT be fed to the continuation (it is an \
         unsound null at a heap-typed `a`); the trampoline must abort first"
    );

    crate::drop::consume_io_tree(crate::handle::test_owned(bind));
}
