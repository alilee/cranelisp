//! IO trampoline — iterative evaluation of IO task trees.
//!
//! The IO model is a deferred-execution system. User code builds IO trees
//! by calling constructors (Pure, Effect) and the `bind` primitive. The
//! trampoline walks the tree iteratively with an explicit continuation
//! stack, avoiding stack overflow for arbitrarily deep bind chains.
//!
//! See `design/backend/io-trampoline.md` for the full design.

use cranelisp_platform::{IO_TAG_BIND, IO_TAG_EFFECT, IO_TAG_PAR, IO_TAG_PURE};
use cranelisp_types::HeapHeader;

use crate::alloc::alloc_with_rc;
use crate::io_trace::{self, IoTracePayload, IoTraceTag};

/// Byte offset of the tag field from the base pointer.
const TAG_OFFSET: isize = HeapHeader::SIZE as isize; // 16

/// Byte offset of the first field from the base pointer.
const FIELD_0_OFFSET: isize = TAG_OFFSET + 8; // 24

/// Byte offset of the second field from the base pointer.
const FIELD_1_OFFSET: isize = FIELD_0_OFFSET + 8; // 32

/// Byte offset of the code pointer within a closure from the base pointer.
/// Closure layout: [header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]
const CLOSURE_CODE_PTR_OFFSET: isize = HeapHeader::SIZE as isize; // 16

/// Force an IO task tree to completion (extern "C" entry point).
///
/// Takes a base pointer to a heap-allocated IO node (Pure/Effect/Bind/Par).
/// Returns the final result value (i64).
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — the top-level IO
/// tree handed to `cranelisp_run_io` is released via
/// `crate::drop::consume_io_tree` after evaluation. The trampoline itself
/// is non-consuming of its input tree (`io_ptr`); it walks the caller's
/// tree read-only. Any IO ADT node produced INSIDE the trampoline by a
/// continuation (Sprint 57 Wave 3 fix per `design/backend/ring2-rc.md`
/// §3.5) is shallow-dec'd inline via `drop::dec_shallow_io`, so continuation
/// intermediates do not leak. Closures reached via the caller's tree are
/// left alone — `consume_io_tree` walks and dec's them transitively.
/// Closures produced INSIDE the trampoline by a continuation (continuation
/// returns a Bind whose cont field is fresh) are also inline-dec'd by the
/// trampoline.
///
/// # Safety
/// `io_ptr` must be a valid base pointer to an IO node with rc > 0.
/// The IO tree must remain live for the duration of this call.
///
/// Linker symbol is `_cranelisp_run_io` (default Rust name via no_mangle) —
/// the standalone startup stub (`__startup.o`) calls into this directly by
/// the Rust function name to drive the IO trampoline, so the export_name
/// MUST remain the unaliased Rust name. JIT side registers it under
/// `runtime/run_io` via function pointer (not linker name).
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_run_io(io_ptr: i64) -> i64 {
    let result = run_io_trampoline(io_ptr);
    // Decision 24: release the caller's tree. `consume_io_tree` transitively
    // walks Pure/Effect/Bind/Par and dec's every heap-typed sub-ref
    // (including continuation closures still owned by Bind nodes).
    // Intermediate nodes produced by the trampoline have already been
    // released by `run_io_trampoline` itself — `io_ptr` is untouched by
    // the trampoline, so this dec is not a double-free.
    crate::drop::consume_io_tree(io_ptr);
    result
}

/// Core trampoline implementation. Separate from the extern "C" wrapper
/// so that panics (on invalid tags) can unwind normally in tests.
///
/// The trampoline is iterative with an explicit continuation stack.
///
/// ## RC balance (Sprint 57 Wave 3; §3.5)
///
/// The trampoline is non-consuming of its input `io_ptr`: nodes reachable
/// through the caller's tree (Bind spine, sub-branches, sub-continuations)
/// are left untouched. The caller (`cranelisp_run_io`, or a Rust-level
/// direct caller) owns the tree and is responsible for releasing it via
/// `drop::consume_io_tree` (or equivalent).
///
/// However, the trampoline IS consuming of any IO ADT node it produces
/// during the walk — specifically, nodes allocated by a continuation's
/// body. A continuation `(fn [x] (pure (+ x 1)))` allocates a fresh Pure
/// when invoked. That Pure becomes the new `current` and, as the
/// trampoline steps further, is replaced — at which point it is
/// shallow-dec'd. Without this inline dec the continuation-produced nodes
/// would leak (O(N) for N Bind steps).
///
/// A `current_is_fresh` flag tracks whether the current node belongs to
/// the caller's tree (initially) or to a continuation-produced subtree
/// (after the first `call_continuation`). It never flips back to false:
/// once we step into a continuation-produced subtree, its sub-nodes
/// (reached via Bind's inner field, Par's branch fields, etc.) are also
/// owned by this trampoline. Closures popped from `cont_stack` that were
/// captured from a fresh Bind are consumed; closures from the caller's
/// tree are left alone.
pub fn run_io_trampoline(io_ptr: i64) -> i64 {
    io_trace::record_event(
        IoTraceTag::TrampolineEnter,
        IoTracePayload::TrampolineEnter { io_ptr },
    );
    let result = run_io_trampoline_inner(io_ptr);
    io_trace::record_event(
        IoTraceTag::TrampolineExit,
        IoTracePayload::TrampolineExit { result },
    );
    result
}

/// Inner loop — all state-machine instrumentation lives here; the outer
/// `run_io_trampoline` wraps it solely to emit enter/exit bookends.
fn run_io_trampoline_inner(io_ptr: i64) -> i64 {
    let mut cont_stack: Vec<(i64, bool)> = Vec::new(); // (cont_ptr, is_fresh)
    let mut current: i64 = io_ptr;
    let mut current_is_fresh: bool = false;

    loop {
        let tag = unsafe { *((current as isize + TAG_OFFSET) as *const i64) };

        match tag {
            t if t == IO_TAG_PURE => {
                let val = unsafe { *((current as isize + FIELD_0_OFFSET) as *const i64) };
                io_trace::record_event(
                    IoTraceTag::PureStep,
                    IoTracePayload::PureStep { value: val, is_fresh: current_is_fresh },
                );
                match cont_stack.pop() {
                    Some((cont_ptr, cont_is_fresh)) => {
                        io_trace::record_event(
                            IoTraceTag::ContPop,
                            IoTracePayload::Cont {
                                cont_ptr,
                                is_fresh: cont_is_fresh,
                                new_depth: cont_stack.len() as u32,
                            },
                        );
                        // Releasing this Pure node: shallow-dec it if we
                        // produced it ourselves (fresh subtree). If it was
                        // part of the caller's tree, leave it to the
                        // caller's post-return `consume_io_tree`.
                        if current_is_fresh {
                            crate::drop::dec_shallow_io(current);
                        }
                        // Same rule for the closure we're about to invoke:
                        // consume it only if it was part of a fresh Bind.
                        let new_io = call_continuation(cont_ptr, val, cont_is_fresh);
                        io_trace::record_event(
                            IoTraceTag::BindExit,
                            IoTracePayload::BindExit { new_current: new_io },
                        );
                        current = new_io;
                        current_is_fresh = true;
                    }
                    None => {
                        // Final node; shallow-dec only if fresh.
                        if current_is_fresh {
                            crate::drop::dec_shallow_io(current);
                        }
                        return val;
                    }
                }
            }
            t if t == IO_TAG_EFFECT => {
                let thunk_ptr =
                    unsafe { *((current as isize + FIELD_0_OFFSET) as *const i64) };
                let resource_token =
                    unsafe { *((current as isize + FIELD_1_OFFSET) as *const i64) };
                // Scheduling class is not currently stored on Effect
                // nodes at runtime — the class attaches to platform
                // symbols at registration time (see
                // `cranelisp-platform::SchedulingClass` and
                // `PlatformFn.scheduling_class`). At the trampoline site
                // we do not have a back-reference to the symbol. Emit 0
                // as a placeholder; Slice 4 can either plumb the class
                // through Effect construction or consume it via /int's
                // scheduler trace.
                //
                // FIXME(/backend): consider threading SchedulingClass
                // into the Effect node payload (extra field) so trampoline
                // events carry the real class without needing a
                // cross-trace correlation. Deferred pending Slice 4
                // evidence.
                io_trace::record_event(
                    IoTraceTag::PlatformEffect,
                    IoTracePayload::PlatformEffect {
                        thunk_ptr,
                        resource_token,
                        scheduling_class: 0,
                    },
                );
                let result = unsafe { cranelisp_platform::call_effect_thunk(thunk_ptr) };
                match cont_stack.pop() {
                    Some((cont_ptr, cont_is_fresh)) => {
                        io_trace::record_event(
                            IoTraceTag::ContPop,
                            IoTracePayload::Cont {
                                cont_ptr,
                                is_fresh: cont_is_fresh,
                                new_depth: cont_stack.len() as u32,
                            },
                        );
                        if current_is_fresh {
                            crate::drop::dec_shallow_io(current);
                        }
                        let new_io = call_continuation(cont_ptr, result, cont_is_fresh);
                        io_trace::record_event(
                            IoTraceTag::BindExit,
                            IoTracePayload::BindExit { new_current: new_io },
                        );
                        current = new_io;
                        current_is_fresh = true;
                    }
                    None => {
                        if current_is_fresh {
                            crate::drop::dec_shallow_io(current);
                        }
                        return result;
                    }
                }
            }
            t if t == IO_TAG_BIND => {
                let inner = unsafe { *((current as isize + FIELD_0_OFFSET) as *const i64) };
                let cont = unsafe { *((current as isize + FIELD_1_OFFSET) as *const i64) };
                io_trace::record_event(
                    IoTraceTag::BindEnter,
                    IoTracePayload::BindEnter {
                        inner_ptr: inner,
                        cont_ptr: cont,
                        is_fresh: current_is_fresh,
                    },
                );
                // The Bind's cont pointer inherits the freshness of the
                // Bind node: caller-tree Binds hold caller-tree conts;
                // fresh Binds (produced by an outer continuation) hold
                // fresh conts.
                cont_stack.push((cont, current_is_fresh));
                io_trace::record_event(
                    IoTraceTag::ContPush,
                    IoTracePayload::Cont {
                        cont_ptr: cont,
                        is_fresh: current_is_fresh,
                        new_depth: cont_stack.len() as u32,
                    },
                );
                if current_is_fresh {
                    // Fresh Bind: shallow-dec the outer Bind alloc; inner
                    // ownership transfers to `current` and remains fresh.
                    crate::drop::dec_shallow_io(current);
                }
                // current_is_fresh stays as-is: if we were fresh, the inner
                // (allocated by the same continuation) is also fresh;
                // if we were not fresh, we're still descending the caller's
                // tree.
                current = inner;
            }
            t if t == IO_TAG_PAR => {
                // Par node layout: [header(16) | tag(8) | count(8) | branch_0(8) | ...]
                let count = unsafe {
                    *((current as isize + FIELD_0_OFFSET) as *const i64)
                } as usize;

                // Read branch IO pointers (at offsets 32, 40, 48, ...)
                let branch_ptrs: Vec<i64> = (0..count)
                    .map(|i| unsafe {
                        *((current as isize + FIELD_1_OFFSET + (i as isize) * 8) as *const i64)
                    })
                    .collect();

                // Dispatch branches. Each branch recursion is itself a
                // non-consuming trampoline run on a caller-tree or
                // fresh-tree branch — it dec's only its own fresh
                // intermediates. The branches themselves are left live for
                // later `consume_io_tree` (caller tree) or shallow-dec'd
                // here (fresh tree) — but §3.5.6 leaves that detail to
                // post-fix refinement; for now we treat branches as owned
                // by their enclosing Par node and let consume_io_tree or
                // the fresh-Par dec at this level release them.
                let parent_ptr = current;
                let results = dispatch_par_branches_with_trace(&branch_ptrs, parent_ptr);
                io_trace::record_event(
                    IoTraceTag::ParJoin,
                    IoTracePayload::ParJoin {
                        parent_ptr,
                        count: count as u32,
                    },
                );

                // Allocate results buffer via alloc_with_rc so the continuation
                // can dec it when done. Results stored at FIELD_0_OFFSET + i*8
                // (offsets 24, 32, 40, ...) matching HeapAdt::field_offset(i).
                let results_buf = alloc_with_rc(8 + count * 8) as i64; // payload: padding(8) + N*8
                for (i, &val) in results.iter().enumerate() {
                    unsafe {
                        *((results_buf as isize + FIELD_0_OFFSET + (i as isize) * 8) as *mut i64) =
                            val;
                    }
                }
                let results_ptr = results_buf;

                // Pop continuation and call with results array pointer
                match cont_stack.pop() {
                    Some((cont_ptr, cont_is_fresh)) => {
                        io_trace::record_event(
                            IoTraceTag::ContPop,
                            IoTracePayload::Cont {
                                cont_ptr,
                                is_fresh: cont_is_fresh,
                                new_depth: cont_stack.len() as u32,
                            },
                        );
                        if current_is_fresh {
                            crate::drop::dec_shallow_io(current);
                        }
                        let new_io = call_continuation(cont_ptr, results_ptr, cont_is_fresh);
                        io_trace::record_event(
                            IoTraceTag::BindExit,
                            IoTracePayload::BindExit { new_current: new_io },
                        );
                        current = new_io;
                        current_is_fresh = true;
                    }
                    None => {
                        if current_is_fresh {
                            crate::drop::dec_shallow_io(current);
                        }
                        return results_ptr;
                    }
                }
            }
            _ => {
                panic!("cranelisp_run_io: unknown IO tag {tag}");
            }
        }
    }
}

/// Call a continuation closure with a value, returning the new IO tree pointer.
///
/// Continuations are Cranelisp closures with standard HeapClosure layout:
/// `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`
///
/// The code_ptr has signature `extern "C" fn(env_ptr: i64, val: i64) -> i64`.
/// The closure pointer itself is passed as the first argument (env_ptr).
///
/// If `cont_is_fresh` is true (the closure belonged to a fresh, trampoline-
/// produced Bind), the closure is consumed after invocation via
/// `drop::consume_closure` so the continuation's one-shot allocation does
/// not leak. If false, the closure is part of the caller's tree and left
/// alone — the caller's post-return `consume_io_tree` walk will release it.
fn call_continuation(cont_ptr: i64, val: i64, cont_is_fresh: bool) -> i64 {
    let code_ptr = unsafe { *((cont_ptr as isize + CLOSURE_CODE_PTR_OFFSET) as *const i64) };
    let call: extern "C" fn(i64, i64) -> i64 =
        unsafe { std::mem::transmute(code_ptr as *const ()) };
    let new_io = call(cont_ptr, val);
    if cont_is_fresh {
        // Continuation-owned closure: release it now. `consume_closure`
        // invokes the embedded drop glue on last-ref and deallocs.
        crate::drop::consume_closure(cont_ptr);
    }
    new_io
}

// --- Par dispatch with resource token serialization ---

/// Read the resource token from an IO node.
///
/// Effect nodes store the token at FIELD_1_OFFSET (offset 32).
/// Non-Effect nodes (Pure, Bind, Par) return 0 (unrestricted).
fn read_resource_token(io_ptr: i64) -> i64 {
    let tag = unsafe { *((io_ptr as isize + TAG_OFFSET) as *const i64) };
    if tag == IO_TAG_EFFECT {
        unsafe { *((io_ptr as isize + FIELD_1_OFFSET) as *const i64) }
    } else {
        0
    }
}

/// Work item for Par dispatch.
enum WorkItem {
    /// A single branch to run independently (token=0).
    Single(usize, i64),
    /// A group of branches to run sequentially (same non-zero resource token).
    SerialGroup(Vec<(usize, i64)>),
}

/// Dispatch Par branches with resource token serialization.
///
/// - Token=0 branches: each dispatched independently to rayon
/// - Same non-zero token: grouped and run sequentially as a single work item
/// - Results are placed in original binding order
///
/// See design/backend/io-scheduling.md §5.2 for the algorithm.
///
/// The `_with_trace` variant used by the trampoline emits `ParSpark` /
/// `ParSerialGroupEnter` events at dispatch time. The original
/// `dispatch_par_branches` remains for any direct callers who prefer not
/// to correlate with a parent node (currently unused in production
/// code).
#[allow(dead_code)]
fn dispatch_par_branches(branch_ptrs: &[i64]) -> Vec<i64> {
    dispatch_par_branches_with_trace(branch_ptrs, 0)
}

fn dispatch_par_branches_with_trace(branch_ptrs: &[i64], parent_ptr: i64) -> Vec<i64> {
    use rayon::prelude::*;
    use std::collections::HashMap;

    // Group branches by resource token.
    let mut token_groups: HashMap<i64, Vec<(usize, i64)>> = HashMap::new();
    for (i, &io_ptr) in branch_ptrs.iter().enumerate() {
        let token = read_resource_token(io_ptr);
        token_groups.entry(token).or_default().push((i, io_ptr));
    }

    // Build work items.
    let mut work_items: Vec<WorkItem> = Vec::new();
    for (&token, entries) in &token_groups {
        if token == 0 {
            // Each unrestricted branch is independent.
            for &(idx, io_ptr) in entries {
                io_trace::record_event(
                    IoTraceTag::ParSpark,
                    IoTracePayload::ParSpark {
                        parent_ptr,
                        branch_idx: idx as u32,
                        token,
                    },
                );
                work_items.push(WorkItem::Single(idx, io_ptr));
            }
        } else {
            // Same non-zero token: run sequentially as one work item.
            io_trace::record_event(
                IoTraceTag::ParSerialGroupEnter,
                IoTracePayload::ParSerialGroupEnter {
                    token,
                    branch_count: entries.len() as u32,
                },
            );
            for &(idx, _io_ptr) in entries {
                io_trace::record_event(
                    IoTraceTag::ParSpark,
                    IoTracePayload::ParSpark {
                        parent_ptr,
                        branch_idx: idx as u32,
                        token,
                    },
                );
            }
            work_items.push(WorkItem::SerialGroup(entries.clone()));
        }
    }

    // Dispatch via rayon and collect results.
    let item_results: Vec<Vec<(usize, i64)>> = work_items
        .into_par_iter()
        .map(|item| match item {
            WorkItem::Single(idx, io_ptr) => {
                let result = run_io_trampoline(io_ptr);
                vec![(idx, result)]
            }
            WorkItem::SerialGroup(entries) => {
                entries
                    .into_iter()
                    .map(|(idx, io_ptr)| {
                        let result = run_io_trampoline(io_ptr);
                        (idx, result)
                    })
                    .collect()
            }
        })
        .collect();

    // Place results in correct positions.
    let mut results = vec![0i64; branch_ptrs.len()];
    for batch in item_results {
        for (idx, val) in batch {
            results[idx] = val;
        }
    }

    results
}

#[cfg(test)]
mod tests {
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
    /// Layout: [header(16) | tag=1(8) | thunk_ptr(8) | resource_token(8)]
    fn make_effect_node(result_value: i64) -> i64 {
        // Double-box a closure that returns the given value.
        let thunk: Box<Box<dyn FnOnce() -> i64>> =
            Box::new(Box::new(move || result_value));
        let thunk_ptr = Box::into_raw(thunk) as i64;

        let base = alloc_with_rc(24); // tag + thunk + resource_token = 24 bytes
        unsafe {
            *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_EFFECT;
            *((base as isize + FIELD_0_OFFSET) as *mut i64) = thunk_ptr;
            *((base as isize + FIELD_1_OFFSET) as *mut i64) = 0; // resource_token
        }
        base as i64
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
            let thunk: Box<Box<dyn FnOnce() -> i64>> =
                Box::new(Box::new(move || {
                    order.lock().unwrap().push(id);
                    id
                }));
            let thunk_ptr = Box::into_raw(thunk) as i64;

            let base = alloc_with_rc(24);
            unsafe {
                *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_EFFECT;
                *((base as isize + FIELD_0_OFFSET) as *mut i64) = thunk_ptr;
                *((base as isize + FIELD_1_OFFSET) as *mut i64) = token;
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

    // spec: 10-io §10.12 — read_resource_token returns 0 for non-Effect nodes
    #[test]
    fn test_read_resource_token() {
        let pure = make_pure_node(42);
        assert_eq!(read_resource_token(pure), 0);

        // Effect with token=5
        let effect = {
            let thunk: Box<Box<dyn FnOnce() -> i64>> =
                Box::new(Box::new(|| 0));
            let thunk_ptr = Box::into_raw(thunk) as i64;
            let base = alloc_with_rc(24);
            unsafe {
                *((base as isize + TAG_OFFSET) as *mut i64) = IO_TAG_EFFECT;
                *((base as isize + FIELD_0_OFFSET) as *mut i64) = thunk_ptr;
                *((base as isize + FIELD_1_OFFSET) as *mut i64) = 5;
            }
            base as i64
        };
        assert_eq!(read_resource_token(effect), 5);
    }
}
